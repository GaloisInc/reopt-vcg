def maxpd1 : instruction :=
  definst "maxpd" $ do
    pattern fun (v_3064 : reg (bv 128)) (v_3065 : reg (bv 128)) => do
      v_6026 <- getRegister v_3065;
      v_6027 <- eval (extract v_6026 0 64);
      v_6028 <- getRegister v_3064;
      v_6029 <- eval (extract v_6028 0 64);
      v_6033 <- eval (extract v_6026 64 128);
      v_6034 <- eval (extract v_6028 64 128);
      setRegister (lhs.of_reg v_3065) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_6027 v_6029) (expression.bv_nat 1 1)) v_6027 v_6029) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_6033 v_6034) (expression.bv_nat 1 1)) v_6033 v_6034));
      pure ()
    pat_end;
    pattern fun (v_3058 : Mem) (v_3060 : reg (bv 128)) => do
      v_9772 <- getRegister v_3060;
      v_9773 <- eval (extract v_9772 0 64);
      v_9774 <- evaluateAddress v_3058;
      v_9775 <- load v_9774 16;
      v_9776 <- eval (extract v_9775 0 64);
      v_9780 <- eval (extract v_9772 64 128);
      v_9781 <- eval (extract v_9775 64 128);
      setRegister (lhs.of_reg v_3060) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9773 v_9776) (expression.bv_nat 1 1)) v_9773 v_9776) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9780 v_9781) (expression.bv_nat 1 1)) v_9780 v_9781));
      pure ()
    pat_end
