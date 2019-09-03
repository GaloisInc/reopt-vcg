def vmaxpd1 : instruction :=
  definst "vmaxpd" $ do
    pattern fun (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) (v_2541 : reg (bv 128)) => do
      v_4318 <- getRegister v_2540;
      v_4319 <- eval (extract v_4318 0 64);
      v_4320 <- getRegister v_2539;
      v_4321 <- eval (extract v_4320 0 64);
      v_4325 <- eval (extract v_4318 64 128);
      v_4326 <- eval (extract v_4320 64 128);
      setRegister (lhs.of_reg v_2541) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4319 v_4321) (expression.bv_nat 1 1)) v_4319 v_4321) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4325 v_4326) (expression.bv_nat 1 1)) v_4325 v_4326));
      pure ()
    pat_end;
    pattern fun (v_2550 : reg (bv 256)) (v_2551 : reg (bv 256)) (v_2552 : reg (bv 256)) => do
      v_4337 <- getRegister v_2551;
      v_4338 <- eval (extract v_4337 0 64);
      v_4339 <- getRegister v_2550;
      v_4340 <- eval (extract v_4339 0 64);
      v_4344 <- eval (extract v_4337 64 128);
      v_4345 <- eval (extract v_4339 64 128);
      v_4349 <- eval (extract v_4337 128 192);
      v_4350 <- eval (extract v_4339 128 192);
      v_4354 <- eval (extract v_4337 192 256);
      v_4355 <- eval (extract v_4339 192 256);
      setRegister (lhs.of_reg v_2552) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4338 v_4340) (expression.bv_nat 1 1)) v_4338 v_4340) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4344 v_4345) (expression.bv_nat 1 1)) v_4344 v_4345) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4349 v_4350) (expression.bv_nat 1 1)) v_4349 v_4350) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4354 v_4355) (expression.bv_nat 1 1)) v_4354 v_4355))));
      pure ()
    pat_end;
    pattern fun (v_2533 : Mem) (v_2534 : reg (bv 128)) (v_2535 : reg (bv 128)) => do
      v_9978 <- getRegister v_2534;
      v_9979 <- eval (extract v_9978 0 64);
      v_9980 <- evaluateAddress v_2533;
      v_9981 <- load v_9980 16;
      v_9982 <- eval (extract v_9981 0 64);
      v_9986 <- eval (extract v_9978 64 128);
      v_9987 <- eval (extract v_9981 64 128);
      setRegister (lhs.of_reg v_2535) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9979 v_9982) (expression.bv_nat 1 1)) v_9979 v_9982) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9986 v_9987) (expression.bv_nat 1 1)) v_9986 v_9987));
      pure ()
    pat_end;
    pattern fun (v_2544 : Mem) (v_2545 : reg (bv 256)) (v_2546 : reg (bv 256)) => do
      v_9993 <- getRegister v_2545;
      v_9994 <- eval (extract v_9993 0 64);
      v_9995 <- evaluateAddress v_2544;
      v_9996 <- load v_9995 32;
      v_9997 <- eval (extract v_9996 0 64);
      v_10001 <- eval (extract v_9993 64 128);
      v_10002 <- eval (extract v_9996 64 128);
      v_10006 <- eval (extract v_9993 128 192);
      v_10007 <- eval (extract v_9996 128 192);
      v_10011 <- eval (extract v_9993 192 256);
      v_10012 <- eval (extract v_9996 192 256);
      setRegister (lhs.of_reg v_2546) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9994 v_9997) (expression.bv_nat 1 1)) v_9994 v_9997) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10001 v_10002) (expression.bv_nat 1 1)) v_10001 v_10002) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10006 v_10007) (expression.bv_nat 1 1)) v_10006 v_10007) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10011 v_10012) (expression.bv_nat 1 1)) v_10011 v_10012))));
      pure ()
    pat_end
