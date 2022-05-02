$(function() {
  $("span.error-short").click(function(){$(this).parents('.error').children(".error-long").toggle()})
  }
)

$(function() {
  $("div.log").dblclick(function(event){
     var error = $(this).nextAll("div.error,div.content-error").first();
     if (error.length > 0) {
       error[0].scrollIntoView();
     }
  })
})

$(function() {
  $("span.sourceref").click(function(){
    var r = $(this).attr("data-mmt-ref");
    var url = 'http://localhost:8080/:action?navigateSource ' + r.replace("#","%23");
    $.ajax({ 'url': url });
  })
})
