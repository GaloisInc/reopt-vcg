def vmaxsd1 : instruction :=
  definst "vmaxsd" $ do
    pattern fun (v_2671 : reg (bv 128)) (v_2672 : reg (bv 128)) (v_2673 : reg (bv 128)) => do
      v_4539 <- getRegister v_2672;
      v_4541 <- eval (extract v_4539 64 128);
      v_4542 <- getRegister v_2671;
      v_4543 <- eval (extract v_4542 64 128);
      setRegister (lhs.of_reg v_2673) (concat (extract v_4539 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4541 v_4543) (expression.bv_nat 1 1)) v_4541 v_4543));
      pure ()
    pat_end;
    pattern fun (v_2666 : Mem) (v_2667 : reg (bv 128)) (v_2668 : reg (bv 128)) => do
      v_9991 <- getRegister v_2667;
      v_9993 <- eval (extract v_9991 64 128);
      v_9994 <- evaluateAddress v_2666;
      v_9995 <- load v_9994 8;
      setRegister (lhs.of_reg v_2668) (concat (extract v_9991 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9993 v_9995) (expression.bv_nat 1 1)) v_9993 v_9995));
      pure ()
    pat_end
