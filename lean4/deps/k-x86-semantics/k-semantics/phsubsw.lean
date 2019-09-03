def phsubsw1 : instruction :=
  definst "phsubsw" $ do
    pattern fun (v_2473 : reg (bv 128)) (v_2474 : reg (bv 128)) => do
      v_4257 <- getRegister v_2473;
      v_4264 <- eval (sub (mi 32 (svalueMInt (extract v_4257 16 32))) (mi 32 (svalueMInt (extract v_4257 0 16))));
      v_4276 <- eval (sub (mi 32 (svalueMInt (extract v_4257 48 64))) (mi 32 (svalueMInt (extract v_4257 32 48))));
      v_4288 <- eval (sub (mi 32 (svalueMInt (extract v_4257 80 96))) (mi 32 (svalueMInt (extract v_4257 64 80))));
      v_4300 <- eval (sub (mi 32 (svalueMInt (extract v_4257 112 128))) (mi 32 (svalueMInt (extract v_4257 96 112))));
      v_4306 <- getRegister v_2474;
      v_4313 <- eval (sub (mi 32 (svalueMInt (extract v_4306 16 32))) (mi 32 (svalueMInt (extract v_4306 0 16))));
      v_4325 <- eval (sub (mi 32 (svalueMInt (extract v_4306 48 64))) (mi 32 (svalueMInt (extract v_4306 32 48))));
      v_4337 <- eval (sub (mi 32 (svalueMInt (extract v_4306 80 96))) (mi 32 (svalueMInt (extract v_4306 64 80))));
      v_4349 <- eval (sub (mi 32 (svalueMInt (extract v_4306 112 128))) (mi 32 (svalueMInt (extract v_4306 96 112))));
      setRegister (lhs.of_reg v_2474) (concat (mux (sgt v_4264 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4264 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4264 16 32))) (concat (mux (sgt v_4276 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4276 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4276 16 32))) (concat (mux (sgt v_4288 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4288 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4288 16 32))) (concat (mux (sgt v_4300 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4300 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4300 16 32))) (concat (mux (sgt v_4313 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4313 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4313 16 32))) (concat (mux (sgt v_4325 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4325 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4325 16 32))) (concat (mux (sgt v_4337 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4337 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4337 16 32))) (mux (sgt v_4349 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4349 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4349 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2468 : Mem) (v_2469 : reg (bv 128)) => do
      v_11706 <- evaluateAddress v_2468;
      v_11707 <- load v_11706 16;
      v_11714 <- eval (sub (mi 32 (svalueMInt (extract v_11707 16 32))) (mi 32 (svalueMInt (extract v_11707 0 16))));
      v_11726 <- eval (sub (mi 32 (svalueMInt (extract v_11707 48 64))) (mi 32 (svalueMInt (extract v_11707 32 48))));
      v_11738 <- eval (sub (mi 32 (svalueMInt (extract v_11707 80 96))) (mi 32 (svalueMInt (extract v_11707 64 80))));
      v_11750 <- eval (sub (mi 32 (svalueMInt (extract v_11707 112 128))) (mi 32 (svalueMInt (extract v_11707 96 112))));
      v_11756 <- getRegister v_2469;
      v_11763 <- eval (sub (mi 32 (svalueMInt (extract v_11756 16 32))) (mi 32 (svalueMInt (extract v_11756 0 16))));
      v_11775 <- eval (sub (mi 32 (svalueMInt (extract v_11756 48 64))) (mi 32 (svalueMInt (extract v_11756 32 48))));
      v_11787 <- eval (sub (mi 32 (svalueMInt (extract v_11756 80 96))) (mi 32 (svalueMInt (extract v_11756 64 80))));
      v_11799 <- eval (sub (mi 32 (svalueMInt (extract v_11756 112 128))) (mi 32 (svalueMInt (extract v_11756 96 112))));
      setRegister (lhs.of_reg v_2469) (concat (mux (sgt v_11714 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11714 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11714 16 32))) (concat (mux (sgt v_11726 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11726 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11726 16 32))) (concat (mux (sgt v_11738 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11738 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11738 16 32))) (concat (mux (sgt v_11750 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11750 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11750 16 32))) (concat (mux (sgt v_11763 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11763 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11763 16 32))) (concat (mux (sgt v_11775 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11775 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11775 16 32))) (concat (mux (sgt v_11787 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11787 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11787 16 32))) (mux (sgt v_11799 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11799 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11799 16 32))))))))));
      pure ()
    pat_end
