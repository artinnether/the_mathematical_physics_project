/* Restore the existing GA4 property. Embedded frames and local previews do not send visits. */
(()=>{
 if(window.self!==window.top||location.hostname!=='artinnether.github.io')return;
 const id='G-Y31PJBLYDM';
 window.dataLayer=window.dataLayer||[];
 window.gtag=window.gtag||function(){window.dataLayer.push(arguments)};
 window.gtag('js',new Date());
 window.gtag('config',id);
 const tag=document.createElement('script');tag.async=true;tag.src='https://www.googletagmanager.com/gtag/js?id='+id;document.head.appendChild(tag);
 let previous;
 window.tmppTrackSection=(section,title)=>{
  if(section===previous)return;
  previous=section;
  window.gtag('event','section_view',{section_id:section,page_title:title});
 };
})();
