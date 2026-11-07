#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Парсер каталога https://yazsm.ru/product/

Обходит все разделы каталога (вместе со страницами пагинации), находит карточки
товаров и сохраняет в CSV: наименование, стоимость, ссылку на изображение (HTTP),
ссылку на товар и раздел.

Защита от блокировок (403 / 429 / проверочные страницы):
  1. браузероподобные заголовки, ротация User-Agent, Referer, cookie-сессия;
  2. случайные паузы и адаптивное замедление: при блокировке пауза растёт, при успехах снова уменьшается;
  3. повторные попытки с экспоненциальной задержкой, учитывается заголовок Retry-After;
  4. смена «личности» (новая сессия, User-Agent, следующий прокси) после каждой блокировки;
  5. автоматический переход на настоящий браузер (Playwright), если requests блокируют;
  6. режим --headed: окно браузера, где проверку/капчу можно пройти вручную;
  7. если блокировка не снимается - скрипт аккуратно останавливается и сохраняет собранное.

Установка:
    pip install requests beautifulsoup4 lxml
    # для режима браузера (необязательно, но рекомендуется держать под рукой):
    pip install playwright
    playwright install chromium

Запуск:
    python parse_yazsm.py
    python parse_yazsm.py --out catalog.csv --delay 1
    python parse_yazsm.py --start https://yazsm.ru/product/borduri/     (только один раздел)
    python parse_yazsm.py --browser always --headed                     (сразу через видимый браузер)
    python parse_yazsm.py --proxy http://user:pass@host:port            (через прокси, можно несколько раз)
    python parse_yazsm.py --debug                                       (сохранить HTML страниц для отладки)
"""

import argparse
import copy
import csv
import os
import random
import re
import sys
import time
from collections import deque
from datetime import datetime
from email.utils import parsedate_to_datetime
from urllib.parse import urljoin, urlparse, urlunparse, parse_qsl, urlencode, unquote

import requests
from bs4 import BeautifulSoup

# --------------------------------------------------------------------------- #
#  Настройки
# --------------------------------------------------------------------------- #

ROOT_URL = "https://yazsm.ru/"
START_URL = "https://yazsm.ru/product/"
HOSTS = {"yazsm.ru", "www.yazsm.ru"}

# Список User-Agent для ротации. Версии браузеров со временем устаревают -
# при желании обновите их на актуальные.
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/141.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/140.0.0.0 Safari/537.36 Edg/140.0.0.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/141.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/141.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:143.0) Gecko/20100101 Firefox/143.0",
]

BASE_HEADERS = {
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "ru-RU,ru;q=0.9,en-US;q=0.6,en;q=0.5",
    "Accept-Encoding": "gzip, deflate",  # без br: requests не умеет распаковывать brotli без доп. пакета
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-User": "?1",
}

# После какой по счёту неудачной попытки подряд подключать браузер (режим --browser auto)
BROWSER_AFTER = 2

# Признаки страницы-заглушки антибот-защиты
BLOCK_MARKERS = (
    "captcha", "qrator", "ddos-guard", "just a moment", "checking your browser",
    "access denied", "are you a robot", "verify you are human",
    "enable javascript and cookies", "проверка браузера", "доступ запрещ",
)

CSV_HEADER = [
    "Наименование",
    "Стоимость",
    "Старая цена",
    "Изображение",
    "Ссылка на товар",
    "Раздел",
]

# Цена: "800 руб.", "от 800 руб./м2", "1 200 руб.", "1050 ₽"
_NUM = r"(?:\d{1,3}(?:[ \u00a0]\d{3})+|\d+)(?:[.,]\d+)?"
PRICE_RE = re.compile(
    r"(?:(?<!\w)от[ \u00a0]+)?" + _NUM + r"[ \u00a0]*(?:руб\.?|₽|р\.)(?:[ \u00a0]*/[ \u00a0]*[\w²³]+)?",
    re.IGNORECASE,
)

# Тексты ссылок/кнопок, которые не являются названием товара
STOP_TEXTS = {
    "подробнее", "сделать заказ", "заказать", "в корзину", "купить",
    "быстрая поставка", "заказать звонок", "в наличии", "под заказ",
}
# Признаки того, что блок - карточка товара (а не плитка раздела)
PRODUCT_HINTS = (
    "в наличии", "под заказ", "сделать заказ", "в корзину",
    "по запросу", "уточняйте", "уточнить",
)
# Картинки-иконки, которые нужно пропускать
JUNK_IMG_WORDS = ("delivery", "icon", "logo", "badge", "sprite")
LAZY_ATTRS = ("data-src", "data-lazy-src", "data-original", "data-lazy", "data-srcset", "srcset", "src")

FILE_EXT_RE = re.compile(r"\.(jpe?g|png|webp|gif|svg|pdf|docx?|xlsx?|zip|rar)$", re.IGNORECASE)
OLD_CLASS_RE = re.compile(r"(^|[_-])old($|[_-])")


# --------------------------------------------------------------------------- #
#  Разбор страниц
# --------------------------------------------------------------------------- #

def clean(text):
    """Убирает неразрывные пробелы и лишние пробелы/переводы строк."""
    return re.sub(r"\s+", " ", (text or "").replace("\u00a0", " ")).strip()


def product_url(href, page_url):
    """Абсолютный URL без query/fragment, если ссылка ведёт в /product/..., иначе None."""
    if not href:
        return None
    href = href.strip()
    if href.startswith(("javascript:", "mailto:", "tel:", "#")):
        return None
    u = urlparse(urljoin(page_url, href))
    if u.netloc.lower() not in HOSTS:
        return None
    if not u.path.startswith("/product/") or "/filter/" in u.path:
        return None
    if FILE_EXT_RE.search(u.path):
        return None
    return urlunparse(("https", "yazsm.ru", u.path, "", "", ""))


def crawl_url(href, page_url):
    """URL для обхода: как product_url, но сохраняет параметры пагинации PAGEN_*."""
    base = product_url(href, page_url)
    if not base:
        return None
    query = urlparse(urljoin(page_url, href.strip())).query
    pagen = [(k, v) for k, v in parse_qsl(query) if k.startswith("PAGEN_")]
    return base + ("?" + urlencode(pagen) if pagen else "")


def image_src(img, page_url):
    """Абсолютный URL картинки (с учётом lazy-load атрибутов) или None."""
    label = " ".join(
        [img.get("alt") or "", img.get("title") or "", " ".join(img.get("class") or [])]
    ).lower()
    if any(w in label for w in JUNK_IMG_WORDS):
        return None
    for attr in ("width", "height"):
        value = (img.get(attr) or "").strip()
        if value.isdigit() and int(value) <= 48:
            return None
    for attr in LAZY_ATTRS:
        value = (img.get(attr) or "").strip()
        if not value:
            continue
        value = value.split(",")[0].strip().split(" ")[0]  # для srcset берём первый URL
        if not value or value.startswith("data:"):
            continue
        if value.lower().split("?")[0].endswith(".svg"):
            return None
        return urljoin(page_url, value)
    return None


def product_image_links(el, page_url):
    """Множество URL товаров, на которые ведут картинки внутри элемента."""
    found = set()
    for img in el.find_all("img"):
        if not image_src(img, page_url):
            continue
        a = img.find_parent("a", href=True)
        if a is not None:
            url = product_url(a["href"], page_url)
            if url:
                found.add(url)
    return found


def title_of(card, url, page_url):
    """Название товара: текст ссылки на этот товар (не 'Подробнее' и т.п.)."""
    best = None
    for a in card.find_all("a", href=True):
        if product_url(a["href"], page_url) != url:
            continue
        text = clean(a.get_text(" ", strip=True))
        if not text or text.lower() in STOP_TEXTS:
            continue
        classes = " ".join((a.get("class") or []) + ((a.parent.get("class") or []) if a.parent else [])).lower()
        preferred = bool(a.find_parent(re.compile(r"^h[1-6]$"))) or "title" in classes or "name" in classes
        prio = 0 if preferred else 1
        if best is None or prio < best[0]:
            best = (prio, text)
    return best[1] if best else ""


def looks_like_product(el):
    text = clean(el.get_text(" ", strip=True))
    low = text.lower()
    return bool(PRICE_RE.search(text)) or any(h in low for h in PRODUCT_HINTS)


def find_card(link, url, page_url):
    """Поднимается от ссылки-картинки вверх, пока не найдёт целую карточку товара."""
    el = link
    for _ in range(10):
        el = el.parent
        if el is None or el.name in ("body", "html", "[document]"):
            return None
        if len(product_image_links(el, page_url)) > 1:
            return None  # вышли за пределы карточки - в блоке уже несколько товаров
        if title_of(el, url, page_url) and looks_like_product(el):
            return el
    return None


def extract_price(card):
    """Возвращает (цена, старая_цена) в виде текста, как на сайте."""
    work = copy.copy(card)

    old_nodes = [
        t for t in work.find_all(True)
        if t.name in ("s", "strike", "del")
        or any(OLD_CLASS_RE.search(c.lower()) for c in (t.get("class") or []))
    ]
    old = ""
    for t in old_nodes:
        m = PRICE_RE.search(clean(t.get_text(" ", strip=True)))
        if m and not old:
            old = clean(m.group(0))
    for t in old_nodes:
        t.extract()

    price = ""
    for t in work.find_all(lambda tag: any("price" in c.lower() for c in (tag.get("class") or []))):
        m = PRICE_RE.search(clean(t.get_text(" ", strip=True)))
        if m:
            price = clean(m.group(0))
            break

    all_prices = []
    for m in PRICE_RE.finditer(clean(work.get_text(" ", strip=True))):
        value = clean(m.group(0))
        if value not in all_prices:
            all_prices.append(value)
    if not price and all_prices:
        price = all_prices[0]
    if not old:
        others = [p for p in all_prices if p != price]
        old = others[0] if others else ""
    return price, old


def card_image(card, url, page_url):
    """Картинка товара: приоритет у картинки внутри ссылки на сам товар."""
    first_any = ""
    for img in card.find_all("img"):
        src = image_src(img, page_url)
        if not src:
            continue
        a = img.find_parent("a", href=True)
        if a is not None and product_url(a["href"], page_url) == url:
            return src
        first_any = first_any or src
    return first_any


def extract_cards(soup, page_url):
    """Находит на странице карточки товаров. Возвращает {url: запись}."""
    result = {}
    for img in soup.find_all("img"):
        if not image_src(img, page_url):
            continue
        link = img.find_parent("a", href=True)
        if link is None:
            continue
        url = product_url(link["href"], page_url)
        if not url or url in result:
            continue
        card = find_card(link, url, page_url)
        if card is None:
            continue
        name = title_of(card, url, page_url) or clean(img.get("alt") or "")
        if not name:
            continue
        price, price_old = extract_price(card)
        result[url] = {
            "name": name,
            "price": price,
            "price_old": price_old,
            "image": card_image(card, url, page_url),
            "url": url,
        }
    return result


# --------------------------------------------------------------------------- #
#  Защита от блокировок: определение блокировки, паузы, браузер
# --------------------------------------------------------------------------- #

class BlockedError(Exception):
    """Сайт не отдаёт страницы ни одним из доступных способов."""


def looks_blocked(status, content):
    """True, если ответ - блокировка / ограничение частоты / страница проверки."""
    if status in (403, 429):
        return True
    text = content[:60000].decode("utf-8", "ignore").lower() if isinstance(content, bytes) else str(content).lower()
    m = re.search(r"<title[^>]*>(.*?)</title>", text, re.S)
    title = m.group(1) if m else ""
    if any(mark in title for mark in BLOCK_MARKERS):
        return True
    has_marker = any(mark in text for mark in BLOCK_MARKERS)
    if status == 503:
        return has_marker
    if status == 200:
        # у обычных страниц сайта большой размер; маленькая страница с "captcha" - это заглушка
        return len(content) < 20000 and has_marker
    return False


def parse_retry_after(value):
    """Заголовок Retry-After (секунды или дата) -> секунды."""
    if not value:
        return 0
    value = value.strip()
    if value.isdigit():
        return int(value)
    try:
        dt = parsedate_to_datetime(value)
        return max(0, (dt - datetime.now(dt.tzinfo)).total_seconds())
    except Exception:
        return 0


def mask_proxy(proxy):
    return re.sub(r"//[^@/]+@", "//***@", proxy)


def playwright_proxy(proxy):
    u = urlparse(proxy)
    cfg = {"server": f"{u.scheme}://{u.hostname}:{u.port}"}
    if u.username:
        cfg["username"] = unquote(u.username)
        cfg["password"] = unquote(u.password or "")
    return cfg


class Throttle:
    """Случайные паузы между запросами; при блокировках растут, при успехах уменьшаются."""

    def __init__(self, delay):
        self.delay = delay
        self.factor = 1.0
        self._first = True

    def wait(self):
        if self._first:
            self._first = False
            return
        time.sleep(self.delay * self.factor * random.uniform(0.6, 1.6))

    def penalize(self):
        self.factor = min(self.factor * 2, 16.0)

    def reward(self):
        self.factor = max(1.0, self.factor * 0.85)


class BrowserFetcher:
    """Загрузка страниц настоящим Chromium (Playwright): проходит JS-проверки, хранит cookie в профиле."""

    def __init__(self, profile_dir, headless, proxy=None):
        from playwright.sync_api import sync_playwright  # импорт здесь, чтобы Playwright был необязателен

        self.headless = headless
        self._pw = sync_playwright().start()
        kwargs = dict(
            user_data_dir=profile_dir,
            headless=headless,
            locale="ru-RU",
            viewport={"width": 1366, "height": 850},
        )
        if proxy:
            kwargs["proxy"] = playwright_proxy(proxy)
        self._ctx = self._pw.chromium.launch_persistent_context(**kwargs)
        self._page = self._ctx.pages[0] if self._ctx.pages else self._ctx.new_page()

    def _read(self):
        try:
            return self._page.content().encode("utf-8")
        except Exception:  # страница в момент перехода
            return b""

    def get(self, url, timeout=45, challenge_wait=25):
        try:
            self._page.goto(url, wait_until="domcontentloaded", timeout=timeout * 1000)
        except Exception as e:
            print(f"  ! Браузер: {str(e).splitlines()[0]}")
            if not self._page.url.startswith(("http://", "https://")):
                return None  # страница не открылась вовсе (нет сети и т.п.) - это не контент сайта
        deadline = time.time() + challenge_wait
        while True:
            data = self._read()
            if data and not looks_blocked(200, data):
                return data
            if time.time() > deadline:
                break
            self._page.wait_for_timeout(1500)  # ждём, пока отработает JS-проверка
        if not self.headless:
            input("  >>> Пройдите проверку/капчу в окне браузера и нажмите Enter здесь... ")
            data = self._read()
            if data and not looks_blocked(200, data):
                return data
        return None

    def close(self):
        try:
            self._ctx.close()
        finally:
            self._pw.stop()


class Fetcher:
    """Загрузчик страниц с защитой от блокировок (см. описание в начале файла)."""

    def __init__(self, delay=0.7, retries=4, proxies=None, browser="auto", headed=False,
                 max_failures=5, max_wait=300, profile_dir=".browser_profile"):
        self.throttle = Throttle(delay)
        self.retries = max(1, retries)
        self.proxies = list(proxies or [])
        self.browser_mode = browser          # auto | never | always
        self.headed = headed
        self.max_failures = max_failures
        self.max_wait = max_wait
        self.profile_dir = profile_dir
        self.use_browser = browser == "always"
        self.failures = 0                    # сколько страниц подряд не удалось получить
        self.session = None
        self._proxy_idx = -1
        self._needs_warmup = True
        self._browser = None
        self._browser_failed = False
        self._new_identity()

    # ---- «личность»: сессия + User-Agent + прокси ---------------------------
    def _current_proxy(self):
        if self.proxies and self._proxy_idx >= 0:
            return self.proxies[self._proxy_idx % len(self.proxies)]
        return None

    def _new_identity(self):
        if self.session is not None:
            self.session.close()
        s = requests.Session()
        s.headers.update(BASE_HEADERS)
        s.headers["User-Agent"] = random.choice(USER_AGENTS)
        if self.proxies:
            self._proxy_idx += 1
            proxy = self._current_proxy()
            s.proxies = {"http": proxy, "https": proxy}
            print(f"  → прокси: {mask_proxy(proxy)}")
        self.session = s
        self._needs_warmup = True

    def _warm_up(self):
        """Заходим на главную, как обычный посетитель: получаем cookie."""
        self._needs_warmup = False
        try:
            self.session.get(ROOT_URL, headers=self._headers(None), timeout=30)
            time.sleep(random.uniform(0.5, 1.5))
        except requests.RequestException:
            pass

    @staticmethod
    def _headers(referer):
        if referer:
            return {"Referer": referer, "Sec-Fetch-Site": "same-origin"}
        return {"Sec-Fetch-Site": "none"}

    # ---- паузы и учёт результатов ---------------------------------------------
    def _sleep_backoff(self, attempt, retry_after=0):
        wait = max(min(5 * 2 ** (attempt - 1), 120), retry_after)
        wait = min(wait, self.max_wait) * random.uniform(0.9, 1.3)
        print(f"  … пауза {wait:.0f} с")
        time.sleep(wait)

    def _success(self):
        self.failures = 0
        self.throttle.reward()

    def _finish(self, url, content):
        if content:
            self._success()
            return content
        self.failures += 1
        print(f"  ✗ Не удалось получить страницу: {url}")
        if self.failures >= self.max_failures:
            raise BlockedError(f"{self.failures} страниц подряд не загрузились")
        return None

    # ---- браузер -----------------------------------------------------------------
    def _browser_get(self, url):
        if self._browser is None:
            if self._browser_failed or self.browser_mode == "never":
                return None
            try:
                self._browser = BrowserFetcher(self.profile_dir, headless=not self.headed,
                                               proxy=self._current_proxy())
            except ImportError:
                print("  ! Для режима браузера установите Playwright: "
                      "pip install playwright && playwright install chromium")
                self._browser_failed = True
                return None
            except Exception as e:
                print(f"  ! Не удалось запустить браузер: {e}")
                self._browser_failed = True
                return None
        return self._browser.get(url)

    # ---- основной метод ----------------------------------------------------------
    def get(self, url, referer=None):
        """Возвращает HTML (bytes) или None. BlockedError - если блокировка не снимается."""
        self.throttle.wait()

        if self.use_browser:
            return self._finish(url, self._browser_get(url))

        if self._needs_warmup:
            self._warm_up()

        for attempt in range(1, self.retries + 1):
            try:
                r = self.session.get(url, headers=self._headers(referer), timeout=30)
            except requests.RequestException as e:
                print(f"  ! Сетевая ошибка: {e} (попытка {attempt}/{self.retries})")
                self._sleep_backoff(attempt)
                continue

            if r.status_code == 404:
                print(f"  ! 404: {url}")
                self._success()
                return None
            if r.status_code == 200 and not looks_blocked(200, r.content):
                self._success()
                return r.content

            if not looks_blocked(r.status_code, r.content):
                # временная ошибка сервера (5xx и т.п.) - просто повторяем позже
                print(f"  ! HTTP {r.status_code}: {url} (попытка {attempt}/{self.retries})")
                self._sleep_backoff(attempt)
                continue

            # ---- блокировка ----
            self.throttle.penalize()
            retry_after = parse_retry_after(r.headers.get("Retry-After"))
            print(f"  ! Блокировка (HTTP {r.status_code}), попытка {attempt}/{self.retries}; "
                  f"паузы между запросами теперь ×{self.throttle.factor:g}")

            if self.browser_mode != "never" and attempt >= BROWSER_AFTER:
                content = self._browser_get(url)
                if content:
                    self.use_browser = True
                    print("  → дальше загружаю страницы через браузер")
                    return self._finish(url, content)

            if attempt < self.retries:
                self._sleep_backoff(attempt, retry_after)
                self._new_identity()   # новая сессия, другой User-Agent, следующий прокси
                self._warm_up()

        return self._finish(url, None)

    def close(self):
        if self._browser is not None:
            try:
                self._browser.close()
            except Exception:
                pass
            self._browser = None
        if self.session is not None:
            self.session.close()


# --------------------------------------------------------------------------- #
#  Обход сайта
# --------------------------------------------------------------------------- #

def make_soup(content):
    try:
        return BeautifulSoup(content, "lxml")
    except Exception:
        return BeautifulSoup(content, "html.parser")


def crawl(start_url, fetcher, max_pages, debug):
    scope = urlparse(start_url).path  # обходим только страницы внутри этого раздела
    queue = deque([(start_url, None)])   # (url, страница-источник для заголовка Referer)
    seen = {start_url}
    card_urls = set()   # страницы самих товаров обходить не нужно
    products = {}       # url -> запись
    pages = 0

    if debug:
        os.makedirs("debug_html", exist_ok=True)

    try:
        while queue and pages < max_pages:
            url, referer = queue.popleft()
            content = fetcher.get(url, referer)
            pages += 1
            if content is None:
                continue
            if debug:
                fname = re.sub(r"[^\w]+", "_", url.replace("https://yazsm.ru", "")).strip("_") or "root"
                with open(os.path.join("debug_html", fname + ".html"), "wb") as f:
                    f.write(content)

            soup = make_soup(content)
            h1 = soup.find("h1")
            category = clean(h1.get_text(" ", strip=True)) if h1 else ""

            cards = extract_cards(soup, url)
            new = 0
            for purl, rec in cards.items():
                card_urls.add(purl)
                if purl not in products:
                    rec["categories"] = []
                    products[purl] = rec
                    new += 1
                if category and category not in products[purl]["categories"]:
                    products[purl]["categories"].append(category)

            for a in soup.find_all("a", href=True):
                link = crawl_url(a["href"], url)
                if not link or link in seen:
                    continue
                path = urlparse(link).path
                if not path.startswith(scope) or link.split("?")[0] in card_urls:
                    continue
                seen.add(link)
                queue.append((link, url))

            print(f"[{pages}] {url}  карточек: {len(cards)}, новых: {new}, "
                  f"в очереди: {len(queue)}, всего товаров: {len(products)}")
    except KeyboardInterrupt:
        print("\nПрервано пользователем - сохраняю то, что уже собрано...")
    except BlockedError as e:
        print(f"\n⛔ Сайт блокирует доступ: {e}.")
        print("   Собранные данные сохраняю. Что можно сделать: подождать и запустить позже; "
              "увеличить --delay; запустить с --browser always --headed (и вручную пройти проверку); "
              "использовать --proxy.")

    return list(products.values())


def save_csv(rows, path, delimiter, encoding):
    with open(path, "w", newline="", encoding=encoding) as f:
        writer = csv.writer(f, delimiter='\t', quoting=csv.QUOTE_MINIMAL)
        writer.writerow(CSV_HEADER)
        for r in rows:
            writer.writerow([
                r["name"],
                r["price"],
                r["price_old"],
                r["image"],
                r["url"],
                " | ".join(r.get("categories", [])),
            ])


def read_proxy_file(path):
    with open(path, encoding="utf-8") as f:
        return [ln.strip() for ln in f if ln.strip() and not ln.lstrip().startswith("#")]


def main():
    p = argparse.ArgumentParser(description="Парсер каталога yazsm.ru -> CSV (UTF-8)")
    p.add_argument("--start", default=START_URL, help="с какого раздела начать (по умолчанию весь каталог)")
    p.add_argument("--out", default="yazsm_products.csv", help="имя CSV-файла")
    p.add_argument("--delimiter", default=";", help="разделитель CSV (для Excel в РФ - ';', иначе ',')")
    p.add_argument("--encoding", default="utf-8-sig",
                   help="кодировка файла: utf-8-sig (UTF-8 с BOM, Excel открывает без «кракозябр») или utf-8")
    p.add_argument("--delay", type=float, default=0.7, help="базовая пауза между запросами, сек (случайная ±)")
    p.add_argument("--max-pages", type=int, default=1000, help="предохранитель: максимум страниц для обхода")
    p.add_argument("--debug", action="store_true", help="сохранять HTML страниц в папку debug_html")

    g = p.add_argument_group("защита от блокировок")
    g.add_argument("--retries", type=int, default=4, help="попыток на страницу (по умолчанию 4)")
    g.add_argument("--max-wait", type=int, default=300, help="максимальная пауза при повторе, сек (по умолчанию 300)")
    g.add_argument("--max-failures", type=int, default=5,
                   help="сколько страниц подряд могут не загрузиться, прежде чем скрипт остановится (по умолчанию 5)")
    g.add_argument("--browser", choices=("auto", "never", "always"), default="auto",
                   help="auto - подключать браузер (Playwright) при блокировках; never - не использовать; "
                        "always - загружать всё через браузер")
    g.add_argument("--headed", action="store_true",
                   help="показывать окно браузера: проверку/капчу можно пройти вручную")
    g.add_argument("--profile-dir", default=".browser_profile",
                   help="папка профиля браузера (cookie сохраняются между запусками)")
    g.add_argument("--proxy", action="append", default=[],
                   help="прокси вида http://user:pass@host:port (можно указать несколько раз)")
    g.add_argument("--proxy-file", help="файл со списком прокси, по одному в строке")
    args = p.parse_args()

    start = crawl_url(args.start, START_URL)
    if not start:
        sys.exit("Стартовый URL должен вести в раздел https://yazsm.ru/product/...")

    proxies = list(args.proxy)
    if args.proxy_file:
        proxies += read_proxy_file(args.proxy_file)

    fetcher = Fetcher(
        delay=args.delay, retries=args.retries, proxies=proxies, browser=args.browser,
        headed=args.headed, max_failures=args.max_failures, max_wait=args.max_wait,
        profile_dir=args.profile_dir,
    )
    try:
        rows = crawl(start, fetcher, args.max_pages, args.debug)
    finally:
        fetcher.close()
    save_csv(rows, args.out, args.delimiter, args.encoding)

    print(f"\nГотово. Товаров: {len(rows)}. Файл: {os.path.abspath(args.out)}")
    if not rows:
        print("Товары не найдены. Запустите с ключом --debug и посмотрите HTML в папке debug_html - "
              "возможно, у сайта изменилась разметка или включена защита от ботов.")


if __name__ == "__main__":
    main()
