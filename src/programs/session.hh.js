module Session(
  connState,
  time,
  logout)
{
  emit connState("connected");
  abort(logout.now || time.nowval > MAX_SESSION_TIME) {
    run Timer(time); 
  }
  emit connState("disconnected"); 
}