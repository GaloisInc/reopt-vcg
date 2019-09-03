def paddsw1 : instruction :=
  definst "paddsw" $ do
    pattern fun (v_3147 : reg (bv 128)) (v_3148 : reg (bv 128)) => do
      v_5994 <- getRegister v_3148;
      v_5998 <- getRegister v_3147;
      v_6002 <- eval (add (mi 32 (svalueMInt (extract v_5994 0 16))) (mi 32 (svalueMInt (extract v_5998 0 16))));
      v_6014 <- eval (add (mi 32 (svalueMInt (extract v_5994 16 32))) (mi 32 (svalueMInt (extract v_5998 16 32))));
      v_6026 <- eval (add (mi 32 (svalueMInt (extract v_5994 32 48))) (mi 32 (svalueMInt (extract v_5998 32 48))));
      v_6038 <- eval (add (mi 32 (svalueMInt (extract v_5994 48 64))) (mi 32 (svalueMInt (extract v_5998 48 64))));
      v_6050 <- eval (add (mi 32 (svalueMInt (extract v_5994 64 80))) (mi 32 (svalueMInt (extract v_5998 64 80))));
      v_6062 <- eval (add (mi 32 (svalueMInt (extract v_5994 80 96))) (mi 32 (svalueMInt (extract v_5998 80 96))));
      v_6074 <- eval (add (mi 32 (svalueMInt (extract v_5994 96 112))) (mi 32 (svalueMInt (extract v_5998 96 112))));
      v_6086 <- eval (add (mi 32 (svalueMInt (extract v_5994 112 128))) (mi 32 (svalueMInt (extract v_5998 112 128))));
      setRegister (lhs.of_reg v_3148) (concat (mux (sgt v_6002 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6002 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6002 16 32))) (concat (mux (sgt v_6014 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6014 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6014 16 32))) (concat (mux (sgt v_6026 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6026 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6026 16 32))) (concat (mux (sgt v_6038 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6038 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6038 16 32))) (concat (mux (sgt v_6050 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6050 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6050 16 32))) (concat (mux (sgt v_6062 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6062 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6062 16 32))) (concat (mux (sgt v_6074 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6074 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6074 16 32))) (mux (sgt v_6086 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6086 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6086 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3142 : Mem) (v_3143 : reg (bv 128)) => do
      v_10078 <- getRegister v_3143;
      v_10082 <- evaluateAddress v_3142;
      v_10083 <- load v_10082 16;
      v_10087 <- eval (add (mi 32 (svalueMInt (extract v_10078 0 16))) (mi 32 (svalueMInt (extract v_10083 0 16))));
      v_10099 <- eval (add (mi 32 (svalueMInt (extract v_10078 16 32))) (mi 32 (svalueMInt (extract v_10083 16 32))));
      v_10111 <- eval (add (mi 32 (svalueMInt (extract v_10078 32 48))) (mi 32 (svalueMInt (extract v_10083 32 48))));
      v_10123 <- eval (add (mi 32 (svalueMInt (extract v_10078 48 64))) (mi 32 (svalueMInt (extract v_10083 48 64))));
      v_10135 <- eval (add (mi 32 (svalueMInt (extract v_10078 64 80))) (mi 32 (svalueMInt (extract v_10083 64 80))));
      v_10147 <- eval (add (mi 32 (svalueMInt (extract v_10078 80 96))) (mi 32 (svalueMInt (extract v_10083 80 96))));
      v_10159 <- eval (add (mi 32 (svalueMInt (extract v_10078 96 112))) (mi 32 (svalueMInt (extract v_10083 96 112))));
      v_10171 <- eval (add (mi 32 (svalueMInt (extract v_10078 112 128))) (mi 32 (svalueMInt (extract v_10083 112 128))));
      setRegister (lhs.of_reg v_3143) (concat (mux (sgt v_10087 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10087 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10087 16 32))) (concat (mux (sgt v_10099 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10099 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10099 16 32))) (concat (mux (sgt v_10111 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10111 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10111 16 32))) (concat (mux (sgt v_10123 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10123 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10123 16 32))) (concat (mux (sgt v_10135 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10135 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10135 16 32))) (concat (mux (sgt v_10147 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10147 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10147 16 32))) (concat (mux (sgt v_10159 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10159 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10159 16 32))) (mux (sgt v_10171 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10171 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10171 16 32))))))))));
      pure ()
    pat_end
