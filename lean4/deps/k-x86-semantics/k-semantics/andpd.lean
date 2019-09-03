def andpd1 : instruction :=
  definst "andpd" $ do
    pattern fun (v_2823 : reg (bv 128)) (v_2824 : reg (bv 128)) => do
      v_5451 <- getRegister v_2824;
      v_5452 <- getRegister v_2823;
      setRegister (lhs.of_reg v_2824) (bv_and v_5451 v_5452);
      pure ()
    pat_end;
    pattern fun (v_2818 : Mem) (v_2819 : reg (bv 128)) => do
      v_9397 <- getRegister v_2819;
      v_9398 <- evaluateAddress v_2818;
      v_9399 <- load v_9398 16;
      setRegister (lhs.of_reg v_2819) (bv_and v_9397 v_9399);
      pure ()
    pat_end
