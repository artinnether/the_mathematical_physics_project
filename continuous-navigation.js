const reader = document.getElementById('reader-frame');
const study = document.getElementById('study-content');
const animation = document.getElementById('study-frame');
const readingHost = document.getElementById('reading-host');
const sidebar = document.querySelector('.sidebar');
const search = document.getElementById('workspace-search');
const shell = document.getElementById('shell');
const menu = document.getElementById('menu-button');
const languageToggle = document.getElementById('language-toggle');
const welcome = document.getElementById('language-welcome');
const links = [...sidebar.querySelectorAll('[data-route]')];
const sections = new Map(links.map(link => [link.dataset.route, link]));
const filterBar = document.querySelector('.section-filters');
const filterButtons = [...filterBar.querySelectorAll('button')];
const categories = new Map([
  ['all', []],
  ['pdfs', ['pdfs']],
  ['animations', ['animations']],
  ['computation', ['computation']],
  ['exercises', ['exercises']],
  ['project', ['about', 'curriculum', 'sesiones-particulares', 'citation', 'contacto',
    'donaciones', 'newsletter', 'contacto-redes']],
]);
const origin = location.origin;
let lang = localStorage.getItem('tmpp-workspace-lang') || 'es';
let active = '';
let category = 'all';

function label(route) {
  return routes[route]?.[lang === 'en' ? 1 : 0] ||
    (lang === 'en' && topicsEN[route]?.title) || topics[route]?.title || route;
}

function revealActiveLink(link) {
  if (link.hidden || !sidebar.clientHeight || document.activeElement === search) return;
  if (link.dataset.route === 'home') {
    sidebar.scrollTop = 0;
    return;
  }
  const bounds = sidebar.getBoundingClientRect();
  const item = link.getBoundingClientRect();
  const inset = 24;
  if (item.top < bounds.top + inset) {
    sidebar.scrollTop += item.top - bounds.top - inset;
  } else if (item.bottom > bounds.bottom - inset) {
    sidebar.scrollTop += item.bottom - bounds.bottom + inset;
  }
}

function displayRoute(route, historyAction) {
  const changed = route !== active;
  active = route;
  const title = label(route);
  document.title = title + ' | The Mathematical Physics Project';
  document.getElementById('view-name').textContent = title;
  for (const link of links) {
    const current = link.dataset.route === route;
    link.classList.toggle('active', current);
    if (current) link.setAttribute('aria-current', 'location');
    else link.removeAttribute('aria-current');
  }
  if (changed) {
    revealActiveLink(sections.get(route));
    window.tmppTrackSection?.(route, document.title);
  }
  if (historyAction) {
    const url = new URL(location.href);
    if (category === 'all') url.searchParams.delete('view');
    else url.searchParams.set('view', category);
    url.hash = route;
    if (url.href !== location.href) history[historyAction + 'State'](null, '', url);
  }
}

function goTo(route, historyAction, focus = false, nextCategory = category) {
  const requested = categories.get(nextCategory);
  if (!sections.has(route)) route = requested[0] || 'home';
  const previousRoute = active;
  const isStudy = Object.hasOwn(topics, route);
  const section = isStudy ? 'animations' : route;
  const previousCategory = category;
  category = requested.length && !requested.includes(section) ? 'all' : nextCategory;
  for (const button of filterButtons) {
    const selected = button.dataset.filterRoute === category;
    button.setAttribute('aria-pressed', String(selected));
    if (selected && previousCategory !== category) {
      button.scrollIntoView({ block: 'nearest', inline: 'nearest' });
    }
  }
  displayRoute(route, historyAction);
  shell.classList.remove('menu-open');
  menu.setAttribute('aria-expanded', 'false');
  reader.hidden = isStudy;
  study.hidden = !isStudy;
  if (isStudy) {
    if (route !== previousRoute) {
      readingHost.scrollTop = 0;
      renderStudy(route);
    }
    return;
  }
  if (Object.hasOwn(topics, previousRoute)) {
    animation.contentWindow.location.replace('about:blank');
    readingHost.scrollTop = 0;
  }
  reader.contentWindow?.postMessage({
    type: 'tmpp-scroll', route, focus, category, visibleRoutes: categories.get(category),
  }, origin);
}

function applyLocation() {
  const route = location.hash.slice(1);
  const view = new URLSearchParams(location.search).get('view');
  const nextCategory = view === 'latest' ? 'pdfs' : view;
  goTo(route === 'latest' ? 'pdfs' : route, 'replace', false,
    categories.has(nextCategory) ? nextCategory : 'all');
}

function renderStudy(route) {
  const topic = (lang === 'en' && topicsEN[route]) || topics[route];
  const fields = ['category', 'heading', 'intro', 'formula', 'instructions', 'note'];
  for (const field of fields) {
    document.getElementById('study-' + field).textContent = topic[field];
  }
  const discussion = (lang === 'en' ? window.TMPP_DISCUSSIONS_EN : window.TMPP_DISCUSSIONS)[route];
  document.getElementById('discussion-before').innerHTML = discussion?.before || '';
  document.getElementById('discussion-after').innerHTML = discussion?.after || '';
  document.getElementById('study-formula').classList.toggle('main-flow-equation', route === 'sphere');
  study.classList.toggle('holonomy-entry', route === 'holonomy');
  animation.style.removeProperty('height');
  let source;
  if (route === 'holonomy') {
    source = 'animations/holonomy.html?v=justified-prose&lang=' + lang +
      '&theme=' + document.documentElement.dataset.theme;
  } else {
    const animationName = route === 'soliton' ? 'soliton-kdv' : route;
    source = 'animations/' + animationName + '-dark.html?v=20261023-en1&lang=' + lang;
  }
  animation.contentWindow.location.replace(new URL(source, document.baseURI));
  animation.title = label(route);
  window.dispatchEvent(new Event('tmpp-entry-change'));
}

function setLang() {
  document.documentElement.lang = lang;
  document.querySelectorAll('[data-es]').forEach(element => {
    element.textContent = element.dataset[lang];
  });
  document.querySelectorAll('[data-href-es][data-href-en]').forEach(link => {
    link.href = link.dataset[lang === 'es' ? 'hrefEs' : 'hrefEn'];
  });
  search.placeholder = lang === 'es' ? 'Buscar una sección…' : 'Find a section…';
  languageToggle.textContent = lang === 'es' ? 'ES / EN' : 'EN / ES';
  filterBar.setAttribute('aria-label', lang === 'es' ? 'Filtrar secciones' : 'Filter sections');
  for (const arrow of document.querySelectorAll('[data-filter-scroll]')) {
    arrow.setAttribute('aria-label', arrow.dataset[lang === 'es' ? 'labelEs' : 'labelEn']);
  }
  localStorage.setItem('tmpp-workspace-lang', lang);
  if (active) displayRoute(active);
  if (Object.hasOwn(topics, active)) renderStudy(active);
  reader.contentWindow?.postMessage({ type: 'tmpp-language', lang }, origin);
}

document.querySelector('.discussion-language').hidden = true;
const resizeAnimation = new ResizeObserver(() => {
  const body = animation.contentDocument?.body;
  if (!body || animation.contentDocument.URL === 'about:blank') return;
  const height = Math.ceil(body.getBoundingClientRect().height);
  if (height > 100) animation.style.height = height + 'px';
});
animation.addEventListener('load', () => {
  resizeAnimation.disconnect();
  if (animation.contentDocument?.body) resizeAnimation.observe(animation.contentDocument.body);
  animation.contentWindow?.postMessage({ type: 'tmpp-language', lang }, origin);
});

history.scrollRestoration = 'manual';
reader.hidden = false;
for (const link of links) {
  link.addEventListener('click', event => goTo(link.dataset.route, 'push', event.detail === 0));
}
for (const button of filterButtons) {
  button.addEventListener('click', () => {
    const view = button.dataset.filterRoute;
    goTo(categories.get(view)[0] || 'home', 'push', false, view);
  });
}
const arrows = [...document.querySelectorAll('[data-filter-scroll]')];
function showAvailableFilterArrows() {
  const atStart = filterBar.scrollLeft < 1;
  const atEnd = filterBar.scrollLeft + filterBar.clientWidth >= filterBar.scrollWidth - 1;
  arrows[0].hidden = atStart;
  arrows[1].hidden = atEnd;
}
for (const arrow of arrows) {
  arrow.addEventListener('click', () => {
    const direction = Number(arrow.dataset.filterScroll);
    const reducedMotion = matchMedia('(prefers-reduced-motion: reduce)').matches;
    filterBar.scrollBy({ left: direction * filterBar.clientWidth * 0.75,
      behavior: reducedMotion ? 'instant' : 'smooth' });
  });
}
filterBar.addEventListener('scroll', showAvailableFilterArrows, { passive: true });
const filterResize = new ResizeObserver(showAvailableFilterArrows);
filterResize.observe(filterBar);
filterButtons.forEach(button => filterResize.observe(button));
for (const link of document.querySelectorAll('.brand, .topbar a[href^="#"]')) {
  link.addEventListener('click', event => {
    event.preventDefault();
    goTo(link.hash.slice(1), 'push', event.detail === 0);
  });
}
window.addEventListener('hashchange', applyLocation);
window.addEventListener('popstate', applyLocation);
window.addEventListener('message', event => {
  if (event.origin !== origin || event.source !== reader.contentWindow) return;
  const data = event.data;
  if (data?.type === 'tmpp-route') goTo(data.route, 'push', data.focus);
  if (data?.type === 'tmpp-position' && !Object.hasOwn(topics, active) &&
      data.category === category && sections.has(data.route)) {
    displayRoute(data.route, 'replace');
  }
});
reader.addEventListener('load', () => {
  reader.contentWindow.postMessage({ type: 'tmpp-language', lang }, origin);
  applyLocation();
});
languageToggle.addEventListener('click', () => {
  lang = lang === 'es' ? 'en' : 'es';
  setLang();
});
search.addEventListener('input', event => {
  const normalize = value => value.toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '');
  const query = normalize(event.target.value);
  let visible = 0;
  sidebar.querySelectorAll('[data-route], [data-route-link]').forEach(link => {
    link.hidden = !normalize(link.textContent).includes(query);
    if (!link.hidden) visible++;
  });
  document.getElementById('empty-nav').style.display = visible ? 'none' : 'block';
});
menu.addEventListener('click', () => {
  const open = shell.classList.toggle('menu-open');
  menu.setAttribute('aria-expanded', String(open));
  if (open && active) revealActiveLink(sections.get(active));
});
welcome.addEventListener('cancel', event => event.preventDefault());
function start() {
  document.documentElement.removeAttribute('data-language-pending');
  setLang();
  applyLocation();
  reader.src = 'reader.html?v=stable-hover&lang=' + lang;
}
for (const button of document.querySelectorAll('[data-entry-language]')) {
  button.addEventListener('click', () => {
    lang = button.dataset.entryLanguage;
    localStorage.setItem('tmpp-language-chosen', '1');
    welcome.close();
    start();
  });
}
if (localStorage.getItem('tmpp-language-chosen') === '1') start();
else welcome.showModal();
