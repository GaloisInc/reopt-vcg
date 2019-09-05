def vmaxpd1 : instruction :=
  definst "vmaxpd" $ do
    pattern fun (v_2602 : reg (bv 128)) (v_2603 : reg (bv 128)) (v_2604 : reg (bv 128)) => do
      v_4376 <- getRegister v_2603;
      v_4377 <- eval (extract v_4376 0 64);
      v_4378 <- getRegister v_2602;
      v_4379 <- eval (extract v_4378 0 64);
      v_4383 <- eval (extract v_4376 64 128);
      v_4384 <- eval (extract v_4378 64 128);
      setRegister (lhs.of_reg v_2604) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4377 v_4379) (expression.bv_nat 1 1)) v_4377 v_4379) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4383 v_4384) (expression.bv_nat 1 1)) v_4383 v_4384));
      pure ()
    pat_end;
    pattern fun (v_2614 : reg (bv 256)) (v_2615 : reg (bv 256)) (v_2616 : reg (bv 256)) => do
      v_4395 <- getRegister v_2615;
      v_4396 <- eval (extract v_4395 0 64);
      v_4397 <- getRegister v_2614;
      v_4398 <- eval (extract v_4397 0 64);
      v_4402 <- eval (extract v_4395 64 128);
      v_4403 <- eval (extract v_4397 64 128);
      v_4407 <- eval (extract v_4395 128 192);
      v_4408 <- eval (extract v_4397 128 192);
      v_4412 <- eval (extract v_4395 192 256);
      v_4413 <- eval (extract v_4397 192 256);
      setRegister (lhs.of_reg v_2616) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4396 v_4398) (expression.bv_nat 1 1)) v_4396 v_4398) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4402 v_4403) (expression.bv_nat 1 1)) v_4402 v_4403) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4407 v_4408) (expression.bv_nat 1 1)) v_4407 v_4408) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4412 v_4413) (expression.bv_nat 1 1)) v_4412 v_4413))));
      pure ()
    pat_end;
    pattern fun (v_2597 : Mem) (v_2598 : reg (bv 128)) (v_2599 : reg (bv 128)) => do
      v_9844 <- getRegister v_2598;
      v_9845 <- eval (extract v_9844 0 64);
      v_9846 <- evaluateAddress v_2597;
      v_9847 <- load v_9846 16;
      v_9848 <- eval (extract v_9847 0 64);
      v_9852 <- eval (extract v_9844 64 128);
      v_9853 <- eval (extract v_9847 64 128);
      setRegister (lhs.of_reg v_2599) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9845 v_9848) (expression.bv_nat 1 1)) v_9845 v_9848) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9852 v_9853) (expression.bv_nat 1 1)) v_9852 v_9853));
      pure ()
    pat_end;
    pattern fun (v_2608 : Mem) (v_2609 : reg (bv 256)) (v_2610 : reg (bv 256)) => do
      v_9859 <- getRegister v_2609;
      v_9860 <- eval (extract v_9859 0 64);
      v_9861 <- evaluateAddress v_2608;
      v_9862 <- load v_9861 32;
      v_9863 <- eval (extract v_9862 0 64);
      v_9867 <- eval (extract v_9859 64 128);
      v_9868 <- eval (extract v_9862 64 128);
      v_9872 <- eval (extract v_9859 128 192);
      v_9873 <- eval (extract v_9862 128 192);
      v_9877 <- eval (extract v_9859 192 256);
      v_9878 <- eval (extract v_9862 192 256);
      setRegister (lhs.of_reg v_2610) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9860 v_9863) (expression.bv_nat 1 1)) v_9860 v_9863) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9867 v_9868) (expression.bv_nat 1 1)) v_9867 v_9868) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9872 v_9873) (expression.bv_nat 1 1)) v_9872 v_9873) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9877 v_9878) (expression.bv_nat 1 1)) v_9877 v_9878))));
      pure ()
    pat_end
