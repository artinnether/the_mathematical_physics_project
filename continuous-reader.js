(() => {
  const origin = location.origin;
  const main = document.querySelector('main');
  const curriculum = document.getElementById('curriculum');
  document.getElementById('about').after(curriculum);

  const initialLang = new URLSearchParams(location.search).get('lang') === 'en' ? 'en' : 'es';

  const home = main.querySelector('.embed-welcome');
  const sections = [...main.querySelectorAll(':scope > section')]
    .filter(section => section.id !== 'project');
  document.body.classList.add('welcome-active');
  sections.forEach(section => section.classList.add('embed-active'));
  const anchors = new Map([['home', home]]);
  for (const section of sections) {
    if (section.id !== 'home-updates') anchors.set(section.id, section);
  }
  setLanguage(initialLang);

  let visibleRoute = '';
  let category = 'all';
  let jumpPosition;
  let scrollCheck = 0;

  function notify(route) {
    if (route === visibleRoute) return;
    visibleRoute = route;
    parent.postMessage({ type: 'tmpp-position', route, category }, origin);
  }

  function showCategory(next, visibleRoutes) {
    if (next === category) return;
    category = next;
    const all = category === 'all';
    const start = visibleRoutes[0];
    home.toggleAttribute('data-filtered-out', !all);
    for (const section of sections) {
      section.toggleAttribute('data-filtered-out', !all && !visibleRoutes.includes(section.id));
      section.toggleAttribute('data-flow-start', section.id === start);
    }
    visibleRoute = '';
  }

  function updateVisibleRoute() {
    scrollCheck = 0;
    if (!visibleRoute || Math.abs(window.scrollY - jumpPosition) < 1) return;
    const line = Math.min(innerHeight * 0.18, 125);
    let route = visibleRoute;
    for (const [id, section] of anchors) {
      const box = section.getBoundingClientRect();
      if (box.height && box.top <= line) route = id;
    }
    const bottom = document.documentElement.scrollHeight - innerHeight;
    if (category === 'all' && bottom > 0 && scrollY >= bottom - 2) route = 'contacto-redes';
    notify(route);
  }

  function scheduleScrollCheck() {
    if (!scrollCheck) scrollCheck = requestAnimationFrame(updateVisibleRoute);
  }

  function jumpTo(route, focus) {
    const section = anchors.get(route);
    if (!section?.getClientRects().length) return;
    const top = route === 'home' ? 0 : scrollY + section.getBoundingClientRect().top;
    window.scrollTo({ top, behavior: 'instant' });
    jumpPosition = scrollY;
    if (focus) {
      const heading = section.querySelector('h1, h2') || section;
      heading.tabIndex = -1;
      heading.focus({ preventScroll: true });
    }
    notify(route);
  }

  window.addEventListener('scroll', scheduleScrollCheck, { passive: true });
  new ResizeObserver(scheduleScrollCheck).observe(main);

  document.addEventListener('click', event => {
    const link = event.target.closest('a[href]');
    if (!link || event.defaultPrevented) return;
    const href = link.getAttribute('href');
    const study = href.match(/^animations\/(holonomy|soliton|sphere|particles)[.-]/)?.[1];
    const route = href.startsWith('#') ? href.slice(1) :
      href === 'laboratorio.html' ? 'animations' : study;
    if (study || anchors.has(route)) {
      event.preventDefault();
      parent.postMessage({ type: 'tmpp-route', route, focus: event.detail === 0 }, origin);
    } else if (!href.startsWith('#') && !link.hasAttribute('download')) {
      link.target = '_blank';
      link.rel = 'noopener noreferrer';
    }
  });

  window.addEventListener('message', event => {
    if (event.origin !== origin || event.source !== parent) return;
    const data = event.data;
    if (data?.type === 'tmpp-language') setLanguage(data.lang);
    if (data?.type === 'tmpp-scroll') {
      showCategory(data.category, data.visibleRoutes);
      jumpTo(data.route, data.focus);
    }
  });
})();
