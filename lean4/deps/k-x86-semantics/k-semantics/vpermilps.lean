def vpermilps1 : instruction :=
  definst "vpermilps" $ do
    pattern fun (v_3031 : imm int) (v_3027 : reg (bv 128)) (v_3028 : reg (bv 128)) => do
      v_8355 <- eval (handleImmediateWithSignExtend v_3031 8 8);
      v_8356 <- eval (extract v_8355 0 2);
      v_8358 <- getRegister v_3027;
      v_8359 <- eval (extract v_8358 96 128);
      v_8361 <- eval (extract v_8358 64 96);
      v_8363 <- eval (extract v_8358 32 64);
      v_8364 <- eval (extract v_8358 0 32);
      v_8368 <- eval (extract v_8355 2 4);
      v_8375 <- eval (extract v_8355 4 6);
      v_8382 <- eval (extract v_8355 6 8);
      setRegister (lhs.of_reg v_3028) (concat (mux (eq v_8356 (expression.bv_nat 2 0)) v_8359 (mux (eq v_8356 (expression.bv_nat 2 1)) v_8361 (mux (eq v_8356 (expression.bv_nat 2 2)) v_8363 v_8364))) (concat (mux (eq v_8368 (expression.bv_nat 2 0)) v_8359 (mux (eq v_8368 (expression.bv_nat 2 1)) v_8361 (mux (eq v_8368 (expression.bv_nat 2 2)) v_8363 v_8364))) (concat (mux (eq v_8375 (expression.bv_nat 2 0)) v_8359 (mux (eq v_8375 (expression.bv_nat 2 1)) v_8361 (mux (eq v_8375 (expression.bv_nat 2 2)) v_8363 v_8364))) (mux (eq v_8382 (expression.bv_nat 2 0)) v_8359 (mux (eq v_8382 (expression.bv_nat 2 1)) v_8361 (mux (eq v_8382 (expression.bv_nat 2 2)) v_8363 v_8364))))));
      pure ()
    pat_end;
    pattern fun (v_3038 : reg (bv 128)) (v_3039 : reg (bv 128)) (v_3040 : reg (bv 128)) => do
      v_8398 <- getRegister v_3038;
      v_8399 <- eval (extract v_8398 30 32);
      v_8401 <- getRegister v_3039;
      v_8402 <- eval (extract v_8401 96 128);
      v_8404 <- eval (extract v_8401 64 96);
      v_8406 <- eval (extract v_8401 32 64);
      v_8407 <- eval (extract v_8401 0 32);
      v_8411 <- eval (extract v_8398 62 64);
      v_8418 <- eval (extract v_8398 94 96);
      v_8425 <- eval (extract v_8398 126 128);
      setRegister (lhs.of_reg v_3040) (concat (mux (eq v_8399 (expression.bv_nat 2 0)) v_8402 (mux (eq v_8399 (expression.bv_nat 2 1)) v_8404 (mux (eq v_8399 (expression.bv_nat 2 2)) v_8406 v_8407))) (concat (mux (eq v_8411 (expression.bv_nat 2 0)) v_8402 (mux (eq v_8411 (expression.bv_nat 2 1)) v_8404 (mux (eq v_8411 (expression.bv_nat 2 2)) v_8406 v_8407))) (concat (mux (eq v_8418 (expression.bv_nat 2 0)) v_8402 (mux (eq v_8418 (expression.bv_nat 2 1)) v_8404 (mux (eq v_8418 (expression.bv_nat 2 2)) v_8406 v_8407))) (mux (eq v_8425 (expression.bv_nat 2 0)) v_8402 (mux (eq v_8425 (expression.bv_nat 2 1)) v_8404 (mux (eq v_8425 (expression.bv_nat 2 2)) v_8406 v_8407))))));
      pure ()
    pat_end;
    pattern fun (v_3051 : imm int) (v_3053 : reg (bv 256)) (v_3054 : reg (bv 256)) => do
      v_8441 <- eval (handleImmediateWithSignExtend v_3051 8 8);
      v_8442 <- eval (extract v_8441 0 2);
      v_8443 <- eval (eq v_8442 (expression.bv_nat 2 0));
      v_8444 <- getRegister v_3053;
      v_8445 <- eval (extract v_8444 96 128);
      v_8446 <- eval (eq v_8442 (expression.bv_nat 2 1));
      v_8447 <- eval (extract v_8444 64 96);
      v_8448 <- eval (eq v_8442 (expression.bv_nat 2 2));
      v_8449 <- eval (extract v_8444 32 64);
      v_8450 <- eval (extract v_8444 0 32);
      v_8454 <- eval (extract v_8441 2 4);
      v_8455 <- eval (eq v_8454 (expression.bv_nat 2 0));
      v_8456 <- eval (eq v_8454 (expression.bv_nat 2 1));
      v_8457 <- eval (eq v_8454 (expression.bv_nat 2 2));
      v_8461 <- eval (extract v_8441 4 6);
      v_8462 <- eval (eq v_8461 (expression.bv_nat 2 0));
      v_8463 <- eval (eq v_8461 (expression.bv_nat 2 1));
      v_8464 <- eval (eq v_8461 (expression.bv_nat 2 2));
      v_8468 <- eval (extract v_8441 6 8);
      v_8469 <- eval (eq v_8468 (expression.bv_nat 2 0));
      v_8470 <- eval (eq v_8468 (expression.bv_nat 2 1));
      v_8471 <- eval (eq v_8468 (expression.bv_nat 2 2));
      v_8475 <- eval (extract v_8444 224 256);
      v_8476 <- eval (extract v_8444 192 224);
      v_8477 <- eval (extract v_8444 160 192);
      v_8478 <- eval (extract v_8444 128 160);
      setRegister (lhs.of_reg v_3054) (concat (mux v_8443 v_8445 (mux v_8446 v_8447 (mux v_8448 v_8449 v_8450))) (concat (mux v_8455 v_8445 (mux v_8456 v_8447 (mux v_8457 v_8449 v_8450))) (concat (mux v_8462 v_8445 (mux v_8463 v_8447 (mux v_8464 v_8449 v_8450))) (concat (mux v_8469 v_8445 (mux v_8470 v_8447 (mux v_8471 v_8449 v_8450))) (concat (mux v_8443 v_8475 (mux v_8446 v_8476 (mux v_8448 v_8477 v_8478))) (concat (mux v_8455 v_8475 (mux v_8456 v_8476 (mux v_8457 v_8477 v_8478))) (concat (mux v_8462 v_8475 (mux v_8463 v_8476 (mux v_8464 v_8477 v_8478))) (mux v_8469 v_8475 (mux v_8470 v_8476 (mux v_8471 v_8477 v_8478))))))))));
      pure ()
    pat_end;
    pattern fun (v_3063 : reg (bv 256)) (v_3064 : reg (bv 256)) (v_3065 : reg (bv 256)) => do
      v_8504 <- getRegister v_3063;
      v_8505 <- eval (extract v_8504 30 32);
      v_8507 <- getRegister v_3064;
      v_8508 <- eval (extract v_8507 96 128);
      v_8510 <- eval (extract v_8507 64 96);
      v_8512 <- eval (extract v_8507 32 64);
      v_8513 <- eval (extract v_8507 0 32);
      v_8517 <- eval (extract v_8504 62 64);
      v_8524 <- eval (extract v_8504 94 96);
      v_8531 <- eval (extract v_8504 126 128);
      v_8538 <- eval (extract v_8504 158 160);
      v_8540 <- eval (extract v_8507 224 256);
      v_8542 <- eval (extract v_8507 192 224);
      v_8544 <- eval (extract v_8507 160 192);
      v_8545 <- eval (extract v_8507 128 160);
      v_8549 <- eval (extract v_8504 190 192);
      v_8556 <- eval (extract v_8504 222 224);
      v_8563 <- eval (extract v_8504 254 256);
      setRegister (lhs.of_reg v_3065) (concat (mux (eq v_8505 (expression.bv_nat 2 0)) v_8508 (mux (eq v_8505 (expression.bv_nat 2 1)) v_8510 (mux (eq v_8505 (expression.bv_nat 2 2)) v_8512 v_8513))) (concat (mux (eq v_8517 (expression.bv_nat 2 0)) v_8508 (mux (eq v_8517 (expression.bv_nat 2 1)) v_8510 (mux (eq v_8517 (expression.bv_nat 2 2)) v_8512 v_8513))) (concat (mux (eq v_8524 (expression.bv_nat 2 0)) v_8508 (mux (eq v_8524 (expression.bv_nat 2 1)) v_8510 (mux (eq v_8524 (expression.bv_nat 2 2)) v_8512 v_8513))) (concat (mux (eq v_8531 (expression.bv_nat 2 0)) v_8508 (mux (eq v_8531 (expression.bv_nat 2 1)) v_8510 (mux (eq v_8531 (expression.bv_nat 2 2)) v_8512 v_8513))) (concat (mux (eq v_8538 (expression.bv_nat 2 0)) v_8540 (mux (eq v_8538 (expression.bv_nat 2 1)) v_8542 (mux (eq v_8538 (expression.bv_nat 2 2)) v_8544 v_8545))) (concat (mux (eq v_8549 (expression.bv_nat 2 0)) v_8540 (mux (eq v_8549 (expression.bv_nat 2 1)) v_8542 (mux (eq v_8549 (expression.bv_nat 2 2)) v_8544 v_8545))) (concat (mux (eq v_8556 (expression.bv_nat 2 0)) v_8540 (mux (eq v_8556 (expression.bv_nat 2 1)) v_8542 (mux (eq v_8556 (expression.bv_nat 2 2)) v_8544 v_8545))) (mux (eq v_8563 (expression.bv_nat 2 0)) v_8540 (mux (eq v_8563 (expression.bv_nat 2 1)) v_8542 (mux (eq v_8563 (expression.bv_nat 2 2)) v_8544 v_8545))))))))));
      pure ()
    pat_end;
    pattern fun (v_3026 : imm int) (v_3025 : Mem) (v_3022 : reg (bv 128)) => do
      v_17125 <- eval (handleImmediateWithSignExtend v_3026 8 8);
      v_17126 <- eval (extract v_17125 0 2);
      v_17128 <- evaluateAddress v_3025;
      v_17129 <- load v_17128 16;
      v_17130 <- eval (extract v_17129 96 128);
      v_17132 <- eval (extract v_17129 64 96);
      v_17134 <- eval (extract v_17129 32 64);
      v_17135 <- eval (extract v_17129 0 32);
      v_17139 <- eval (extract v_17125 2 4);
      v_17146 <- eval (extract v_17125 4 6);
      v_17153 <- eval (extract v_17125 6 8);
      setRegister (lhs.of_reg v_3022) (concat (mux (eq v_17126 (expression.bv_nat 2 0)) v_17130 (mux (eq v_17126 (expression.bv_nat 2 1)) v_17132 (mux (eq v_17126 (expression.bv_nat 2 2)) v_17134 v_17135))) (concat (mux (eq v_17139 (expression.bv_nat 2 0)) v_17130 (mux (eq v_17139 (expression.bv_nat 2 1)) v_17132 (mux (eq v_17139 (expression.bv_nat 2 2)) v_17134 v_17135))) (concat (mux (eq v_17146 (expression.bv_nat 2 0)) v_17130 (mux (eq v_17146 (expression.bv_nat 2 1)) v_17132 (mux (eq v_17146 (expression.bv_nat 2 2)) v_17134 v_17135))) (mux (eq v_17153 (expression.bv_nat 2 0)) v_17130 (mux (eq v_17153 (expression.bv_nat 2 1)) v_17132 (mux (eq v_17153 (expression.bv_nat 2 2)) v_17134 v_17135))))));
      pure ()
    pat_end;
    pattern fun (v_3037 : Mem) (v_3033 : reg (bv 128)) (v_3034 : reg (bv 128)) => do
      v_17164 <- evaluateAddress v_3037;
      v_17165 <- load v_17164 16;
      v_17166 <- eval (extract v_17165 30 32);
      v_17168 <- getRegister v_3033;
      v_17169 <- eval (extract v_17168 96 128);
      v_17171 <- eval (extract v_17168 64 96);
      v_17173 <- eval (extract v_17168 32 64);
      v_17174 <- eval (extract v_17168 0 32);
      v_17178 <- eval (extract v_17165 62 64);
      v_17185 <- eval (extract v_17165 94 96);
      v_17192 <- eval (extract v_17165 126 128);
      setRegister (lhs.of_reg v_3034) (concat (mux (eq v_17166 (expression.bv_nat 2 0)) v_17169 (mux (eq v_17166 (expression.bv_nat 2 1)) v_17171 (mux (eq v_17166 (expression.bv_nat 2 2)) v_17173 v_17174))) (concat (mux (eq v_17178 (expression.bv_nat 2 0)) v_17169 (mux (eq v_17178 (expression.bv_nat 2 1)) v_17171 (mux (eq v_17178 (expression.bv_nat 2 2)) v_17173 v_17174))) (concat (mux (eq v_17185 (expression.bv_nat 2 0)) v_17169 (mux (eq v_17185 (expression.bv_nat 2 1)) v_17171 (mux (eq v_17185 (expression.bv_nat 2 2)) v_17173 v_17174))) (mux (eq v_17192 (expression.bv_nat 2 0)) v_17169 (mux (eq v_17192 (expression.bv_nat 2 1)) v_17171 (mux (eq v_17192 (expression.bv_nat 2 2)) v_17173 v_17174))))));
      pure ()
    pat_end;
    pattern fun (v_3047 : imm int) (v_3046 : Mem) (v_3048 : reg (bv 256)) => do
      v_17203 <- eval (handleImmediateWithSignExtend v_3047 8 8);
      v_17204 <- eval (extract v_17203 0 2);
      v_17205 <- eval (eq v_17204 (expression.bv_nat 2 0));
      v_17206 <- evaluateAddress v_3046;
      v_17207 <- load v_17206 32;
      v_17208 <- eval (extract v_17207 96 128);
      v_17209 <- eval (eq v_17204 (expression.bv_nat 2 1));
      v_17210 <- eval (extract v_17207 64 96);
      v_17211 <- eval (eq v_17204 (expression.bv_nat 2 2));
      v_17212 <- eval (extract v_17207 32 64);
      v_17213 <- eval (extract v_17207 0 32);
      v_17217 <- eval (extract v_17203 2 4);
      v_17218 <- eval (eq v_17217 (expression.bv_nat 2 0));
      v_17219 <- eval (eq v_17217 (expression.bv_nat 2 1));
      v_17220 <- eval (eq v_17217 (expression.bv_nat 2 2));
      v_17224 <- eval (extract v_17203 4 6);
      v_17225 <- eval (eq v_17224 (expression.bv_nat 2 0));
      v_17226 <- eval (eq v_17224 (expression.bv_nat 2 1));
      v_17227 <- eval (eq v_17224 (expression.bv_nat 2 2));
      v_17231 <- eval (extract v_17203 6 8);
      v_17232 <- eval (eq v_17231 (expression.bv_nat 2 0));
      v_17233 <- eval (eq v_17231 (expression.bv_nat 2 1));
      v_17234 <- eval (eq v_17231 (expression.bv_nat 2 2));
      v_17238 <- eval (extract v_17207 224 256);
      v_17239 <- eval (extract v_17207 192 224);
      v_17240 <- eval (extract v_17207 160 192);
      v_17241 <- eval (extract v_17207 128 160);
      setRegister (lhs.of_reg v_3048) (concat (mux v_17205 v_17208 (mux v_17209 v_17210 (mux v_17211 v_17212 v_17213))) (concat (mux v_17218 v_17208 (mux v_17219 v_17210 (mux v_17220 v_17212 v_17213))) (concat (mux v_17225 v_17208 (mux v_17226 v_17210 (mux v_17227 v_17212 v_17213))) (concat (mux v_17232 v_17208 (mux v_17233 v_17210 (mux v_17234 v_17212 v_17213))) (concat (mux v_17205 v_17238 (mux v_17209 v_17239 (mux v_17211 v_17240 v_17241))) (concat (mux v_17218 v_17238 (mux v_17219 v_17239 (mux v_17220 v_17240 v_17241))) (concat (mux v_17225 v_17238 (mux v_17226 v_17239 (mux v_17227 v_17240 v_17241))) (mux v_17232 v_17238 (mux v_17233 v_17239 (mux v_17234 v_17240 v_17241))))))))));
      pure ()
    pat_end;
    pattern fun (v_3057 : Mem) (v_3058 : reg (bv 256)) (v_3059 : reg (bv 256)) => do
      v_17262 <- evaluateAddress v_3057;
      v_17263 <- load v_17262 32;
      v_17264 <- eval (extract v_17263 30 32);
      v_17266 <- getRegister v_3058;
      v_17267 <- eval (extract v_17266 96 128);
      v_17269 <- eval (extract v_17266 64 96);
      v_17271 <- eval (extract v_17266 32 64);
      v_17272 <- eval (extract v_17266 0 32);
      v_17276 <- eval (extract v_17263 62 64);
      v_17283 <- eval (extract v_17263 94 96);
      v_17290 <- eval (extract v_17263 126 128);
      v_17297 <- eval (extract v_17263 158 160);
      v_17299 <- eval (extract v_17266 224 256);
      v_17301 <- eval (extract v_17266 192 224);
      v_17303 <- eval (extract v_17266 160 192);
      v_17304 <- eval (extract v_17266 128 160);
      v_17308 <- eval (extract v_17263 190 192);
      v_17315 <- eval (extract v_17263 222 224);
      v_17322 <- eval (extract v_17263 254 256);
      setRegister (lhs.of_reg v_3059) (concat (mux (eq v_17264 (expression.bv_nat 2 0)) v_17267 (mux (eq v_17264 (expression.bv_nat 2 1)) v_17269 (mux (eq v_17264 (expression.bv_nat 2 2)) v_17271 v_17272))) (concat (mux (eq v_17276 (expression.bv_nat 2 0)) v_17267 (mux (eq v_17276 (expression.bv_nat 2 1)) v_17269 (mux (eq v_17276 (expression.bv_nat 2 2)) v_17271 v_17272))) (concat (mux (eq v_17283 (expression.bv_nat 2 0)) v_17267 (mux (eq v_17283 (expression.bv_nat 2 1)) v_17269 (mux (eq v_17283 (expression.bv_nat 2 2)) v_17271 v_17272))) (concat (mux (eq v_17290 (expression.bv_nat 2 0)) v_17267 (mux (eq v_17290 (expression.bv_nat 2 1)) v_17269 (mux (eq v_17290 (expression.bv_nat 2 2)) v_17271 v_17272))) (concat (mux (eq v_17297 (expression.bv_nat 2 0)) v_17299 (mux (eq v_17297 (expression.bv_nat 2 1)) v_17301 (mux (eq v_17297 (expression.bv_nat 2 2)) v_17303 v_17304))) (concat (mux (eq v_17308 (expression.bv_nat 2 0)) v_17299 (mux (eq v_17308 (expression.bv_nat 2 1)) v_17301 (mux (eq v_17308 (expression.bv_nat 2 2)) v_17303 v_17304))) (concat (mux (eq v_17315 (expression.bv_nat 2 0)) v_17299 (mux (eq v_17315 (expression.bv_nat 2 1)) v_17301 (mux (eq v_17315 (expression.bv_nat 2 2)) v_17303 v_17304))) (mux (eq v_17322 (expression.bv_nat 2 0)) v_17299 (mux (eq v_17322 (expression.bv_nat 2 1)) v_17301 (mux (eq v_17322 (expression.bv_nat 2 2)) v_17303 v_17304))))))))));
      pure ()
    pat_end
