def vmaxps1 : instruction :=
  definst "vmaxps" $ do
    pattern fun (v_2649 : reg (bv 128)) (v_2650 : reg (bv 128)) (v_2651 : reg (bv 128)) => do
      v_4453 <- getRegister v_2650;
      v_4454 <- eval (extract v_4453 0 32);
      v_4455 <- getRegister v_2649;
      v_4456 <- eval (extract v_4455 0 32);
      v_4460 <- eval (extract v_4453 32 64);
      v_4461 <- eval (extract v_4455 32 64);
      v_4465 <- eval (extract v_4453 64 96);
      v_4466 <- eval (extract v_4455 64 96);
      v_4470 <- eval (extract v_4453 96 128);
      v_4471 <- eval (extract v_4455 96 128);
      setRegister (lhs.of_reg v_2651) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4454 v_4456) (expression.bv_nat 1 1)) v_4454 v_4456) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4460 v_4461) (expression.bv_nat 1 1)) v_4460 v_4461) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4465 v_4466) (expression.bv_nat 1 1)) v_4465 v_4466) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4470 v_4471) (expression.bv_nat 1 1)) v_4470 v_4471))));
      pure ()
    pat_end;
    pattern fun (v_2660 : reg (bv 256)) (v_2661 : reg (bv 256)) (v_2662 : reg (bv 256)) => do
      v_4484 <- getRegister v_2661;
      v_4485 <- eval (extract v_4484 0 32);
      v_4486 <- getRegister v_2660;
      v_4487 <- eval (extract v_4486 0 32);
      v_4491 <- eval (extract v_4484 32 64);
      v_4492 <- eval (extract v_4486 32 64);
      v_4496 <- eval (extract v_4484 64 96);
      v_4497 <- eval (extract v_4486 64 96);
      v_4501 <- eval (extract v_4484 96 128);
      v_4502 <- eval (extract v_4486 96 128);
      v_4506 <- eval (extract v_4484 128 160);
      v_4507 <- eval (extract v_4486 128 160);
      v_4511 <- eval (extract v_4484 160 192);
      v_4512 <- eval (extract v_4486 160 192);
      v_4516 <- eval (extract v_4484 192 224);
      v_4517 <- eval (extract v_4486 192 224);
      v_4521 <- eval (extract v_4484 224 256);
      v_4522 <- eval (extract v_4486 224 256);
      setRegister (lhs.of_reg v_2662) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4485 v_4487) (expression.bv_nat 1 1)) v_4485 v_4487) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4491 v_4492) (expression.bv_nat 1 1)) v_4491 v_4492) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4496 v_4497) (expression.bv_nat 1 1)) v_4496 v_4497) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4501 v_4502) (expression.bv_nat 1 1)) v_4501 v_4502) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4506 v_4507) (expression.bv_nat 1 1)) v_4506 v_4507) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4511 v_4512) (expression.bv_nat 1 1)) v_4511 v_4512) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4516 v_4517) (expression.bv_nat 1 1)) v_4516 v_4517) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4521 v_4522) (expression.bv_nat 1 1)) v_4521 v_4522))))))));
      pure ()
    pat_end;
    pattern fun (v_2644 : Mem) (v_2645 : reg (bv 128)) (v_2646 : reg (bv 128)) => do
      v_9913 <- getRegister v_2645;
      v_9914 <- eval (extract v_9913 0 32);
      v_9915 <- evaluateAddress v_2644;
      v_9916 <- load v_9915 16;
      v_9917 <- eval (extract v_9916 0 32);
      v_9921 <- eval (extract v_9913 32 64);
      v_9922 <- eval (extract v_9916 32 64);
      v_9926 <- eval (extract v_9913 64 96);
      v_9927 <- eval (extract v_9916 64 96);
      v_9931 <- eval (extract v_9913 96 128);
      v_9932 <- eval (extract v_9916 96 128);
      setRegister (lhs.of_reg v_2646) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9914 v_9917) (expression.bv_nat 1 1)) v_9914 v_9917) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9921 v_9922) (expression.bv_nat 1 1)) v_9921 v_9922) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9926 v_9927) (expression.bv_nat 1 1)) v_9926 v_9927) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9931 v_9932) (expression.bv_nat 1 1)) v_9931 v_9932))));
      pure ()
    pat_end;
    pattern fun (v_2655 : Mem) (v_2656 : reg (bv 256)) (v_2657 : reg (bv 256)) => do
      v_9940 <- getRegister v_2656;
      v_9941 <- eval (extract v_9940 0 32);
      v_9942 <- evaluateAddress v_2655;
      v_9943 <- load v_9942 32;
      v_9944 <- eval (extract v_9943 0 32);
      v_9948 <- eval (extract v_9940 32 64);
      v_9949 <- eval (extract v_9943 32 64);
      v_9953 <- eval (extract v_9940 64 96);
      v_9954 <- eval (extract v_9943 64 96);
      v_9958 <- eval (extract v_9940 96 128);
      v_9959 <- eval (extract v_9943 96 128);
      v_9963 <- eval (extract v_9940 128 160);
      v_9964 <- eval (extract v_9943 128 160);
      v_9968 <- eval (extract v_9940 160 192);
      v_9969 <- eval (extract v_9943 160 192);
      v_9973 <- eval (extract v_9940 192 224);
      v_9974 <- eval (extract v_9943 192 224);
      v_9978 <- eval (extract v_9940 224 256);
      v_9979 <- eval (extract v_9943 224 256);
      setRegister (lhs.of_reg v_2657) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9941 v_9944) (expression.bv_nat 1 1)) v_9941 v_9944) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9948 v_9949) (expression.bv_nat 1 1)) v_9948 v_9949) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9953 v_9954) (expression.bv_nat 1 1)) v_9953 v_9954) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9958 v_9959) (expression.bv_nat 1 1)) v_9958 v_9959) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9963 v_9964) (expression.bv_nat 1 1)) v_9963 v_9964) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9968 v_9969) (expression.bv_nat 1 1)) v_9968 v_9969) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9973 v_9974) (expression.bv_nat 1 1)) v_9973 v_9974) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9978 v_9979) (expression.bv_nat 1 1)) v_9978 v_9979))))))));
      pure ()
    pat_end
