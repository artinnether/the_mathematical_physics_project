/* Existing GA4 property. Local previews and embedded page views are excluded. */
(()=>{
 if(location.hostname!=='artinnether.github.io')return;
 const embedded=window.self!==window.top;
 function paperEvent(anchor){
  let url;try{url=new URL(anchor.href,location.href)}catch{return null}
  if(url.origin!==location.origin||!url.pathname.toLowerCase().endsWith('.pdf'))return null;
  const card=anchor.closest('.resource-card,article');
  const title=card?.querySelector('h2,h3,h4')?.textContent?.trim()||anchor.getAttribute('aria-label')||url.pathname.split('/').pop();
  let filename;try{filename=decodeURIComponent(url.pathname)}catch{filename=url.pathname}
  return {event:anchor.hasAttribute('download')?'paper_download':'paper_open',file_name:filename,file_extension:'pdf',link_url:url.origin+url.pathname,document_title:title.slice(0,100),language:document.documentElement.lang||'es'};
 }
 function record(data){
  if(!['paper_open','paper_download'].includes(data?.event)||typeof data.link_url!=='string')return;
  let url;try{url=new URL(data.link_url)}catch{return}
  if(url.origin!==location.origin||!url.pathname.toLowerCase().endsWith('.pdf'))return;
  let filename;try{filename=decodeURIComponent(url.pathname)}catch{filename=url.pathname}
  window.gtag('event',data.event,{file_name:filename,file_extension:'pdf',link_url:url.origin+url.pathname,document_title:String(data.document_title||'').slice(0,100),language:data.language==='en'?'en':'es',section_id:location.hash.slice(1)||'home',transport_type:'beacon'});
 }
 document.addEventListener('click',event=>{
  if(event.button!==0)return;
  const anchor=event.target.closest?.('a[href]');if(!anchor)return;
  const data=paperEvent(anchor);if(!data)return;
  if(embedded)window.parent.postMessage({type:'tmpp-paper-event',...data},location.origin);else record(data);
 },true);
 if(embedded)return;
 const id='G-Y31PJBLYDM';
 window.dataLayer=window.dataLayer||[];
 window.gtag=window.gtag||function(){window.dataLayer.push(arguments)};
 window.gtag('js',new Date());
 window.gtag('config',id);
 const tag=document.createElement('script');tag.async=true;tag.src='https://www.googletagmanager.com/gtag/js?id='+id;document.head.appendChild(tag);
 window.addEventListener('message',event=>{
  if(event.origin!==location.origin||event.data?.type!=='tmpp-paper-event')return;
  if(!Array.from(document.querySelectorAll('iframe')).some(frame=>frame.contentWindow===event.source))return;
  record(event.data);
 });
 let previous;
 window.tmppTrackSection=(section,title)=>{
  if(section===previous)return;
  previous=section;
  window.gtag('event','section_view',{section_id:section,page_title:title});
 };
})();
