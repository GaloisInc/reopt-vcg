def phaddsw1 : instruction :=
  definst "phaddsw" $ do
    pattern fun (v_2437 : reg (bv 128)) (v_2438 : reg (bv 128)) => do
      v_4051 <- getRegister v_2437;
      v_4058 <- eval (add (mi 32 (svalueMInt (extract v_4051 0 16))) (mi 32 (svalueMInt (extract v_4051 16 32))));
      v_4070 <- eval (add (mi 32 (svalueMInt (extract v_4051 32 48))) (mi 32 (svalueMInt (extract v_4051 48 64))));
      v_4082 <- eval (add (mi 32 (svalueMInt (extract v_4051 64 80))) (mi 32 (svalueMInt (extract v_4051 80 96))));
      v_4094 <- eval (add (mi 32 (svalueMInt (extract v_4051 96 112))) (mi 32 (svalueMInt (extract v_4051 112 128))));
      v_4100 <- getRegister v_2438;
      v_4107 <- eval (add (mi 32 (svalueMInt (extract v_4100 0 16))) (mi 32 (svalueMInt (extract v_4100 16 32))));
      v_4119 <- eval (add (mi 32 (svalueMInt (extract v_4100 32 48))) (mi 32 (svalueMInt (extract v_4100 48 64))));
      v_4131 <- eval (add (mi 32 (svalueMInt (extract v_4100 64 80))) (mi 32 (svalueMInt (extract v_4100 80 96))));
      v_4143 <- eval (add (mi 32 (svalueMInt (extract v_4100 112 128))) (mi 32 (svalueMInt (extract v_4100 96 112))));
      setRegister (lhs.of_reg v_2438) (concat (mux (sgt v_4058 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4058 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4058 16 32))) (concat (mux (sgt v_4070 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4070 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4070 16 32))) (concat (mux (sgt v_4082 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4082 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4082 16 32))) (concat (mux (sgt v_4094 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4094 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4094 16 32))) (concat (mux (sgt v_4107 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4107 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4107 16 32))) (concat (mux (sgt v_4119 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4119 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4119 16 32))) (concat (mux (sgt v_4131 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4131 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4131 16 32))) (mux (sgt v_4143 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4143 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4143 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2432 : Mem) (v_2433 : reg (bv 128)) => do
      v_11512 <- evaluateAddress v_2432;
      v_11513 <- load v_11512 16;
      v_11520 <- eval (add (mi 32 (svalueMInt (extract v_11513 0 16))) (mi 32 (svalueMInt (extract v_11513 16 32))));
      v_11532 <- eval (add (mi 32 (svalueMInt (extract v_11513 32 48))) (mi 32 (svalueMInt (extract v_11513 48 64))));
      v_11544 <- eval (add (mi 32 (svalueMInt (extract v_11513 64 80))) (mi 32 (svalueMInt (extract v_11513 80 96))));
      v_11556 <- eval (add (mi 32 (svalueMInt (extract v_11513 96 112))) (mi 32 (svalueMInt (extract v_11513 112 128))));
      v_11562 <- getRegister v_2433;
      v_11569 <- eval (add (mi 32 (svalueMInt (extract v_11562 0 16))) (mi 32 (svalueMInt (extract v_11562 16 32))));
      v_11581 <- eval (add (mi 32 (svalueMInt (extract v_11562 32 48))) (mi 32 (svalueMInt (extract v_11562 48 64))));
      v_11593 <- eval (add (mi 32 (svalueMInt (extract v_11562 64 80))) (mi 32 (svalueMInt (extract v_11562 80 96))));
      v_11605 <- eval (add (mi 32 (svalueMInt (extract v_11562 112 128))) (mi 32 (svalueMInt (extract v_11562 96 112))));
      setRegister (lhs.of_reg v_2433) (concat (mux (sgt v_11520 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11520 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11520 16 32))) (concat (mux (sgt v_11532 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11532 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11532 16 32))) (concat (mux (sgt v_11544 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11544 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11544 16 32))) (concat (mux (sgt v_11556 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11556 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11556 16 32))) (concat (mux (sgt v_11569 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11569 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11569 16 32))) (concat (mux (sgt v_11581 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11581 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11581 16 32))) (concat (mux (sgt v_11593 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11593 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11593 16 32))) (mux (sgt v_11605 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11605 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11605 16 32))))))))));
      pure ()
    pat_end
