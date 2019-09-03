def vmaxps1 : instruction :=
  definst "vmaxps" $ do
    pattern fun (v_2561 : reg (bv 128)) (v_2562 : reg (bv 128)) (v_2563 : reg (bv 128)) => do
      v_4368 <- getRegister v_2562;
      v_4369 <- eval (extract v_4368 0 32);
      v_4370 <- getRegister v_2561;
      v_4371 <- eval (extract v_4370 0 32);
      v_4375 <- eval (extract v_4368 32 64);
      v_4376 <- eval (extract v_4370 32 64);
      v_4380 <- eval (extract v_4368 64 96);
      v_4381 <- eval (extract v_4370 64 96);
      v_4385 <- eval (extract v_4368 96 128);
      v_4386 <- eval (extract v_4370 96 128);
      setRegister (lhs.of_reg v_2563) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4369 v_4371) (expression.bv_nat 1 1)) v_4369 v_4371) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4375 v_4376) (expression.bv_nat 1 1)) v_4375 v_4376) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4380 v_4381) (expression.bv_nat 1 1)) v_4380 v_4381) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4385 v_4386) (expression.bv_nat 1 1)) v_4385 v_4386))));
      pure ()
    pat_end;
    pattern fun (v_2572 : reg (bv 256)) (v_2573 : reg (bv 256)) (v_2574 : reg (bv 256)) => do
      v_4399 <- getRegister v_2573;
      v_4400 <- eval (extract v_4399 0 32);
      v_4401 <- getRegister v_2572;
      v_4402 <- eval (extract v_4401 0 32);
      v_4406 <- eval (extract v_4399 32 64);
      v_4407 <- eval (extract v_4401 32 64);
      v_4411 <- eval (extract v_4399 64 96);
      v_4412 <- eval (extract v_4401 64 96);
      v_4416 <- eval (extract v_4399 96 128);
      v_4417 <- eval (extract v_4401 96 128);
      v_4421 <- eval (extract v_4399 128 160);
      v_4422 <- eval (extract v_4401 128 160);
      v_4426 <- eval (extract v_4399 160 192);
      v_4427 <- eval (extract v_4401 160 192);
      v_4431 <- eval (extract v_4399 192 224);
      v_4432 <- eval (extract v_4401 192 224);
      v_4436 <- eval (extract v_4399 224 256);
      v_4437 <- eval (extract v_4401 224 256);
      setRegister (lhs.of_reg v_2574) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4400 v_4402) (expression.bv_nat 1 1)) v_4400 v_4402) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4406 v_4407) (expression.bv_nat 1 1)) v_4406 v_4407) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4411 v_4412) (expression.bv_nat 1 1)) v_4411 v_4412) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4416 v_4417) (expression.bv_nat 1 1)) v_4416 v_4417) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4421 v_4422) (expression.bv_nat 1 1)) v_4421 v_4422) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4426 v_4427) (expression.bv_nat 1 1)) v_4426 v_4427) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4431 v_4432) (expression.bv_nat 1 1)) v_4431 v_4432) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4436 v_4437) (expression.bv_nat 1 1)) v_4436 v_4437))))))));
      pure ()
    pat_end;
    pattern fun (v_2555 : Mem) (v_2556 : reg (bv 128)) (v_2557 : reg (bv 128)) => do
      v_10020 <- getRegister v_2556;
      v_10021 <- eval (extract v_10020 0 32);
      v_10022 <- evaluateAddress v_2555;
      v_10023 <- load v_10022 16;
      v_10024 <- eval (extract v_10023 0 32);
      v_10028 <- eval (extract v_10020 32 64);
      v_10029 <- eval (extract v_10023 32 64);
      v_10033 <- eval (extract v_10020 64 96);
      v_10034 <- eval (extract v_10023 64 96);
      v_10038 <- eval (extract v_10020 96 128);
      v_10039 <- eval (extract v_10023 96 128);
      setRegister (lhs.of_reg v_2557) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10021 v_10024) (expression.bv_nat 1 1)) v_10021 v_10024) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10028 v_10029) (expression.bv_nat 1 1)) v_10028 v_10029) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10033 v_10034) (expression.bv_nat 1 1)) v_10033 v_10034) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10038 v_10039) (expression.bv_nat 1 1)) v_10038 v_10039))));
      pure ()
    pat_end;
    pattern fun (v_2566 : Mem) (v_2567 : reg (bv 256)) (v_2568 : reg (bv 256)) => do
      v_10047 <- getRegister v_2567;
      v_10048 <- eval (extract v_10047 0 32);
      v_10049 <- evaluateAddress v_2566;
      v_10050 <- load v_10049 32;
      v_10051 <- eval (extract v_10050 0 32);
      v_10055 <- eval (extract v_10047 32 64);
      v_10056 <- eval (extract v_10050 32 64);
      v_10060 <- eval (extract v_10047 64 96);
      v_10061 <- eval (extract v_10050 64 96);
      v_10065 <- eval (extract v_10047 96 128);
      v_10066 <- eval (extract v_10050 96 128);
      v_10070 <- eval (extract v_10047 128 160);
      v_10071 <- eval (extract v_10050 128 160);
      v_10075 <- eval (extract v_10047 160 192);
      v_10076 <- eval (extract v_10050 160 192);
      v_10080 <- eval (extract v_10047 192 224);
      v_10081 <- eval (extract v_10050 192 224);
      v_10085 <- eval (extract v_10047 224 256);
      v_10086 <- eval (extract v_10050 224 256);
      setRegister (lhs.of_reg v_2568) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10048 v_10051) (expression.bv_nat 1 1)) v_10048 v_10051) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10055 v_10056) (expression.bv_nat 1 1)) v_10055 v_10056) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10060 v_10061) (expression.bv_nat 1 1)) v_10060 v_10061) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10065 v_10066) (expression.bv_nat 1 1)) v_10065 v_10066) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10070 v_10071) (expression.bv_nat 1 1)) v_10070 v_10071) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10075 v_10076) (expression.bv_nat 1 1)) v_10075 v_10076) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10080 v_10081) (expression.bv_nat 1 1)) v_10080 v_10081) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10085 v_10086) (expression.bv_nat 1 1)) v_10085 v_10086))))))));
      pure ()
    pat_end
