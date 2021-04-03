hiphop module Identity(
  in name,
  in passwd, out enableLogin) 
{
  do{
    emit enableLogin(
      name.nowval.length>=2 && passwd.nowval.length>=2); 
  } every(name.now || passwd.now)
}