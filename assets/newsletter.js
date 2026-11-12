const subscription = document.getElementById('newsletterForm');
const subscribeButton = subscription.querySelector('button[type="submit"]');
const subscriptionStatus = document.getElementById('newsletter-status');

const subscriptionMessages = {
  sending: ['Enviando tu solicitud…', 'Sending your request…'],
  success: ['Recibimos tu solicitud de suscripción.', 'We received your subscription request.'],
  error: ['No pudimos enviar tu solicitud. Inténtalo de nuevo.', 'We could not send your request. Please try again.'],
};

function showSubscriptionStatus(state) {
  const [es, en] = subscriptionMessages[state];
  subscriptionStatus.dataset.state = state;
  subscriptionStatus.dataset.langEs = es;
  subscriptionStatus.dataset.langEn = en;
  subscriptionStatus.textContent = document.documentElement.lang === 'es' ? es : en;
}

subscription.addEventListener('submit', async (event) => {
  event.preventDefault();
  if (subscribeButton.disabled) return;

  const data = new FormData(subscription);
  subscribeButton.disabled = true;
  showSubscriptionStatus('sending');

  try {
    const response = await fetch(subscription.action, {
      method: subscription.method,
      body: data,
      headers: { Accept: 'application/json' },
      signal: AbortSignal.timeout(15000),
    });

    if (!response.ok) throw new Error('Subscription request failed');

    subscription.reset();
    showSubscriptionStatus('success');
  } catch {
    showSubscriptionStatus('error');
  } finally {
    subscribeButton.disabled = false;
  }
});
