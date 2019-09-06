def phaddsw1 : instruction :=
  definst "phaddsw" $ do
    pattern fun (v_2528 : reg (bv 128)) (v_2529 : reg (bv 128)) => do
      v_4142 <- getRegister v_2528;
      v_4147 <- eval (add (sext (extract v_4142 0 16) 32) (sext (extract v_4142 16 32) 32));
      v_4157 <- eval (add (sext (extract v_4142 32 48) 32) (sext (extract v_4142 48 64) 32));
      v_4167 <- eval (add (sext (extract v_4142 64 80) 32) (sext (extract v_4142 80 96) 32));
      v_4177 <- eval (add (sext (extract v_4142 96 112) 32) (sext (extract v_4142 112 128) 32));
      v_4183 <- getRegister v_2529;
      v_4188 <- eval (add (sext (extract v_4183 0 16) 32) (sext (extract v_4183 16 32) 32));
      v_4198 <- eval (add (sext (extract v_4183 32 48) 32) (sext (extract v_4183 48 64) 32));
      v_4208 <- eval (add (sext (extract v_4183 64 80) 32) (sext (extract v_4183 80 96) 32));
      v_4218 <- eval (add (sext (extract v_4183 112 128) 32) (sext (extract v_4183 96 112) 32));
      setRegister (lhs.of_reg v_2529) (concat (mux (sgt v_4147 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4147 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4147 16 32))) (concat (mux (sgt v_4157 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4157 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4157 16 32))) (concat (mux (sgt v_4167 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4167 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4167 16 32))) (concat (mux (sgt v_4177 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4177 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4177 16 32))) (concat (mux (sgt v_4188 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4188 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4188 16 32))) (concat (mux (sgt v_4198 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4198 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4198 16 32))) (concat (mux (sgt v_4208 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4208 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4208 16 32))) (mux (sgt v_4218 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4218 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4218 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2524 : Mem) (v_2525 : reg (bv 128)) => do
      v_11048 <- evaluateAddress v_2524;
      v_11049 <- load v_11048 16;
      v_11054 <- eval (add (sext (extract v_11049 0 16) 32) (sext (extract v_11049 16 32) 32));
      v_11064 <- eval (add (sext (extract v_11049 32 48) 32) (sext (extract v_11049 48 64) 32));
      v_11074 <- eval (add (sext (extract v_11049 64 80) 32) (sext (extract v_11049 80 96) 32));
      v_11084 <- eval (add (sext (extract v_11049 96 112) 32) (sext (extract v_11049 112 128) 32));
      v_11090 <- getRegister v_2525;
      v_11095 <- eval (add (sext (extract v_11090 0 16) 32) (sext (extract v_11090 16 32) 32));
      v_11105 <- eval (add (sext (extract v_11090 32 48) 32) (sext (extract v_11090 48 64) 32));
      v_11115 <- eval (add (sext (extract v_11090 64 80) 32) (sext (extract v_11090 80 96) 32));
      v_11125 <- eval (add (sext (extract v_11090 112 128) 32) (sext (extract v_11090 96 112) 32));
      setRegister (lhs.of_reg v_2525) (concat (mux (sgt v_11054 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11054 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11054 16 32))) (concat (mux (sgt v_11064 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11064 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11064 16 32))) (concat (mux (sgt v_11074 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11074 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11074 16 32))) (concat (mux (sgt v_11084 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11084 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11084 16 32))) (concat (mux (sgt v_11095 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11095 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11095 16 32))) (concat (mux (sgt v_11105 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11105 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11105 16 32))) (concat (mux (sgt v_11115 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11115 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11115 16 32))) (mux (sgt v_11125 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11125 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11125 16 32))))))))));
      pure ()
    pat_end
