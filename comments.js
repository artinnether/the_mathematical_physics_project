(()=>{
 const form=document.getElementById('public-comment-form'),list=document.getElementById('approved-comments'),status=document.getElementById('comment-status');
 if(!form)return;
 const keys=new Set(['soliton','sphere','particles','holonomy']);
 let revision=0;
 const es=()=>document.documentElement.lang!=='en';
 const entry=()=>form.dataset.entry||location.hash.slice(1);
 const pageUrl=key=>form.dataset.pageUrl||'https://artinnether.github.io/the_mathematical_physics_project/#'+key;
 async function render(){
  const token=++revision,key=entry();form.reset();status.textContent='';form.elements.entry.value=key;form.elements.page_url.value=pageUrl(key);list.replaceChildren();
  if(!keys.has(key))return;
  try{
   const response=await fetch(form.dataset.commentsUrl||'approved-comments.json',{cache:'no-cache'});if(!response.ok)throw Error('load');const data=await response.json();if(token!==revision)return;
   const comments=Array.isArray(data[key])?data[key]:[];
   const heading=document.createElement('p');heading.textContent=comments.length?(es()?`${comments.length} comentarios publicados`:`${comments.length} published comments`):(es()?'Todavía no hay comentarios publicados.':'No published comments yet.');list.append(heading);
   for(const comment of comments){const article=document.createElement('article');article.className='approved-comment';const name=document.createElement('strong');name.textContent=String(comment.name||'');const body=document.createElement('p');body.textContent=String(comment.message||'');article.append(name,body);list.append(article)}
  }catch{if(token===revision)list.textContent=es()?'No se pudieron cargar los comentarios publicados.':'Published comments could not be loaded.'}
 }
 form.addEventListener('submit',async event=>{
  event.preventDefault();if(!form.reportValidity()||!keys.has(entry()))return;
  const token=revision,key=entry(),data=new FormData(form);if(String(data.get('name')).trim()===''||String(data.get('message')).trim()===''){status.textContent=es()?'Escribe tu nombre y comentario.':'Enter your name and comment.';return}
  const button=form.querySelector('button[type=submit]');if(button.disabled)return;button.disabled=true;status.textContent=es()?'Enviando…':'Sending…';
  try{const response=await fetch(form.action,{method:'POST',body:data,headers:{Accept:'application/json'}});if(!response.ok)throw Error('send');if(token===revision&&entry()===key){form.reset();form.elements.entry.value=key;form.elements.page_url.value=pageUrl(key);status.textContent=es()?'Comentario enviado para revisión. Aparecerá aquí después de ser aprobado y publicado.':'Comment submitted for review. It will appear here after approval and publication.'}}
  catch{if(token===revision)status.textContent=es()?'No se pudo enviar. Tu texto sigue en el formulario; inténtalo de nuevo.':'Could not send. Your text is still in the form; please try again.'}
  finally{button.disabled=false}
 });
 window.addEventListener('hashchange',render);window.addEventListener('tmpp-entry-change',render);render();
})();
