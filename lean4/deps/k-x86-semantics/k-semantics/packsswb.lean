def packsswb1 : instruction :=
  definst "packsswb" $ do
    pattern fun (v_3084 : reg (bv 128)) (v_3085 : reg (bv 128)) => do
      v_5376 <- getRegister v_3084;
      v_5377 <- eval (extract v_5376 0 16);
      v_5383 <- eval (extract v_5376 16 32);
      v_5389 <- eval (extract v_5376 32 48);
      v_5395 <- eval (extract v_5376 48 64);
      v_5401 <- eval (extract v_5376 64 80);
      v_5407 <- eval (extract v_5376 80 96);
      v_5413 <- eval (extract v_5376 96 112);
      v_5419 <- eval (extract v_5376 112 128);
      v_5425 <- getRegister v_3085;
      v_5426 <- eval (extract v_5425 0 16);
      v_5432 <- eval (extract v_5425 16 32);
      v_5438 <- eval (extract v_5425 32 48);
      v_5444 <- eval (extract v_5425 48 64);
      v_5450 <- eval (extract v_5425 64 80);
      v_5456 <- eval (extract v_5425 80 96);
      v_5462 <- eval (extract v_5425 96 112);
      v_5468 <- eval (extract v_5425 112 128);
      setRegister (lhs.of_reg v_3085) (concat (mux (sgt v_5377 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5377 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 8 16))) (concat (mux (sgt v_5383 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5383 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 24 32))) (concat (mux (sgt v_5389 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5389 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 40 48))) (concat (mux (sgt v_5395 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5395 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 56 64))) (concat (mux (sgt v_5401 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5401 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 72 80))) (concat (mux (sgt v_5407 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5407 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 88 96))) (concat (mux (sgt v_5413 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5413 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 104 112))) (concat (mux (sgt v_5419 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5419 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5376 120 128))) (concat (mux (sgt v_5426 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5426 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 8 16))) (concat (mux (sgt v_5432 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5432 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 24 32))) (concat (mux (sgt v_5438 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5438 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 40 48))) (concat (mux (sgt v_5444 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5444 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 56 64))) (concat (mux (sgt v_5450 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5450 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 72 80))) (concat (mux (sgt v_5456 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5456 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 88 96))) (concat (mux (sgt v_5462 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5462 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 104 112))) (mux (sgt v_5468 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5468 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5425 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) (v_3080 : reg (bv 128)) => do
      v_9481 <- evaluateAddress v_3079;
      v_9482 <- load v_9481 16;
      v_9483 <- eval (extract v_9482 0 16);
      v_9489 <- eval (extract v_9482 16 32);
      v_9495 <- eval (extract v_9482 32 48);
      v_9501 <- eval (extract v_9482 48 64);
      v_9507 <- eval (extract v_9482 64 80);
      v_9513 <- eval (extract v_9482 80 96);
      v_9519 <- eval (extract v_9482 96 112);
      v_9525 <- eval (extract v_9482 112 128);
      v_9531 <- getRegister v_3080;
      v_9532 <- eval (extract v_9531 0 16);
      v_9538 <- eval (extract v_9531 16 32);
      v_9544 <- eval (extract v_9531 32 48);
      v_9550 <- eval (extract v_9531 48 64);
      v_9556 <- eval (extract v_9531 64 80);
      v_9562 <- eval (extract v_9531 80 96);
      v_9568 <- eval (extract v_9531 96 112);
      v_9574 <- eval (extract v_9531 112 128);
      setRegister (lhs.of_reg v_3080) (concat (mux (sgt v_9483 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9483 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 8 16))) (concat (mux (sgt v_9489 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9489 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 24 32))) (concat (mux (sgt v_9495 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9495 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 40 48))) (concat (mux (sgt v_9501 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9501 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 56 64))) (concat (mux (sgt v_9507 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9507 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 72 80))) (concat (mux (sgt v_9513 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9513 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 88 96))) (concat (mux (sgt v_9519 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9519 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 104 112))) (concat (mux (sgt v_9525 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9525 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9482 120 128))) (concat (mux (sgt v_9532 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9532 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 8 16))) (concat (mux (sgt v_9538 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9538 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 24 32))) (concat (mux (sgt v_9544 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9544 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 40 48))) (concat (mux (sgt v_9550 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9550 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 56 64))) (concat (mux (sgt v_9556 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9556 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 72 80))) (concat (mux (sgt v_9562 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9562 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 88 96))) (concat (mux (sgt v_9568 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9568 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 104 112))) (mux (sgt v_9574 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9574 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9531 120 128))))))))))))))))));
      pure ()
    pat_end
