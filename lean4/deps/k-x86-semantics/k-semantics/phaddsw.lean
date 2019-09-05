def phaddsw1 : instruction :=
  definst "phaddsw" $ do
    pattern fun (v_2500 : reg (bv 128)) (v_2501 : reg (bv 128)) => do
      v_4115 <- getRegister v_2500;
      v_4120 <- eval (add (sext (extract v_4115 0 16) 32) (sext (extract v_4115 16 32) 32));
      v_4130 <- eval (add (sext (extract v_4115 32 48) 32) (sext (extract v_4115 48 64) 32));
      v_4140 <- eval (add (sext (extract v_4115 64 80) 32) (sext (extract v_4115 80 96) 32));
      v_4150 <- eval (add (sext (extract v_4115 96 112) 32) (sext (extract v_4115 112 128) 32));
      v_4156 <- getRegister v_2501;
      v_4161 <- eval (add (sext (extract v_4156 0 16) 32) (sext (extract v_4156 16 32) 32));
      v_4171 <- eval (add (sext (extract v_4156 32 48) 32) (sext (extract v_4156 48 64) 32));
      v_4181 <- eval (add (sext (extract v_4156 64 80) 32) (sext (extract v_4156 80 96) 32));
      v_4191 <- eval (add (sext (extract v_4156 112 128) 32) (sext (extract v_4156 96 112) 32));
      setRegister (lhs.of_reg v_2501) (concat (mux (sgt v_4120 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4120 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4120 16 32))) (concat (mux (sgt v_4130 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4130 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4130 16 32))) (concat (mux (sgt v_4140 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4140 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4140 16 32))) (concat (mux (sgt v_4150 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4150 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4150 16 32))) (concat (mux (sgt v_4161 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4161 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4161 16 32))) (concat (mux (sgt v_4171 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4171 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4171 16 32))) (concat (mux (sgt v_4181 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4181 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4181 16 32))) (mux (sgt v_4191 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4191 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4191 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2497 : Mem) (v_2496 : reg (bv 128)) => do
      v_11072 <- evaluateAddress v_2497;
      v_11073 <- load v_11072 16;
      v_11078 <- eval (add (sext (extract v_11073 0 16) 32) (sext (extract v_11073 16 32) 32));
      v_11088 <- eval (add (sext (extract v_11073 32 48) 32) (sext (extract v_11073 48 64) 32));
      v_11098 <- eval (add (sext (extract v_11073 64 80) 32) (sext (extract v_11073 80 96) 32));
      v_11108 <- eval (add (sext (extract v_11073 96 112) 32) (sext (extract v_11073 112 128) 32));
      v_11114 <- getRegister v_2496;
      v_11119 <- eval (add (sext (extract v_11114 0 16) 32) (sext (extract v_11114 16 32) 32));
      v_11129 <- eval (add (sext (extract v_11114 32 48) 32) (sext (extract v_11114 48 64) 32));
      v_11139 <- eval (add (sext (extract v_11114 64 80) 32) (sext (extract v_11114 80 96) 32));
      v_11149 <- eval (add (sext (extract v_11114 112 128) 32) (sext (extract v_11114 96 112) 32));
      setRegister (lhs.of_reg v_2496) (concat (mux (sgt v_11078 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11078 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11078 16 32))) (concat (mux (sgt v_11088 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11088 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11088 16 32))) (concat (mux (sgt v_11098 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11098 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11098 16 32))) (concat (mux (sgt v_11108 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11108 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11108 16 32))) (concat (mux (sgt v_11119 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11119 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11119 16 32))) (concat (mux (sgt v_11129 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11129 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11129 16 32))) (concat (mux (sgt v_11139 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11139 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11139 16 32))) (mux (sgt v_11149 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11149 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11149 16 32))))))))));
      pure ()
    pat_end
