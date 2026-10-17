/* Each animation has a stable discussion key independent of language and theme. */
(()=>{
 const keys=new Set(['soliton','sphere','particles']);
 const host=document.getElementById('entry-comments-widget');
 if(!host)return;
 let generation=0,observer;
 const config=fetch('comments-config.json').then(r=>{if(!r.ok)throw Error('config');return r.json()}).catch(()=>null);
 const current=()=>location.hash.slice(1);
 const theme=()=>document.documentElement.dataset.theme==='dark'?'dark':'light';
 function sync(){const f=host.querySelector('iframe.giscus-frame');f?.contentWindow?.postMessage({giscus:{setConfig:{theme:theme(),lang:document.documentElement.lang==='en'?'en':'es'}}},'https://giscus.app')}
 async function render(){
  const token=++generation,key=current();observer?.disconnect();host.replaceChildren();
  const fallback=document.getElementById('entry-comments-fallback');fallback.hidden=false;
  if(!keys.has(key))return;
  const c=await config;if(token!==generation||!c?.repoId||!c?.categoryId)return;
  host.id=key;fallback.hidden=true;
  let backlink=document.querySelector('meta[name="giscus:backlink"]');if(!backlink){backlink=document.createElement('meta');backlink.name='giscus:backlink';document.head.append(backlink)}backlink.content='https://artinnether.github.io/the_mathematical_physics_project/#'+key;
  observer=new IntersectionObserver(entries=>{if(!entries.some(e=>e.isIntersecting))return;observer.disconnect();if(token!==generation)return;
   const script=document.createElement('script');script.src='https://giscus.app/client.js';script.async=true;script.crossOrigin='anonymous';
   const attrs={repo:c.repo,'repo-id':c.repoId,category:c.category,'category-id':c.categoryId,mapping:'specific',term:'tmpp-animation-'+key,strict:'1','reactions-enabled':'1','emit-metadata':'0','input-position':'top',theme:theme(),lang:document.documentElement.lang==='en'?'en':'es',loading:'lazy'};
   for(const [k,v]of Object.entries(attrs))script.setAttribute('data-'+k,v);
   script.onerror=()=>{fallback.hidden=false};host.append(script);
  },{rootMargin:'200px'});observer.observe(host);
 }
 window.addEventListener('message',e=>{if(e.origin!=='https://giscus.app'||e.source!==host.querySelector('iframe')?.contentWindow)return;if(e.data?.giscus?.error&&!/discussion not found/i.test(e.data.giscus.error))document.getElementById('entry-comments-fallback').hidden=false;});
 new MutationObserver(()=>{sync();if(host.querySelector('iframe'))document.getElementById('entry-comments-fallback').hidden=true}).observe(host,{childList:true});
 new MutationObserver(sync).observe(document.documentElement,{attributes:true,attributeFilter:['data-theme','lang']});
 window.addEventListener('hashchange',render);window.addEventListener('tmpp-entry-change',render);render();
})();
