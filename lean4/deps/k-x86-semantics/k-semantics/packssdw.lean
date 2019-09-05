def packssdw1 : instruction :=
  definst "packssdw" $ do
    pattern fun (v_3138 : reg (bv 128)) (v_3139 : reg (bv 128)) => do
      v_5258 <- getRegister v_3138;
      v_5259 <- eval (extract v_5258 0 32);
      v_5265 <- eval (extract v_5258 32 64);
      v_5271 <- eval (extract v_5258 64 96);
      v_5277 <- eval (extract v_5258 96 128);
      v_5283 <- getRegister v_3139;
      v_5284 <- eval (extract v_5283 0 32);
      v_5290 <- eval (extract v_5283 32 64);
      v_5296 <- eval (extract v_5283 64 96);
      v_5302 <- eval (extract v_5283 96 128);
      setRegister (lhs.of_reg v_3139) (concat (mux (sgt v_5259 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5259 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5258 16 32))) (concat (mux (sgt v_5265 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5265 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5258 48 64))) (concat (mux (sgt v_5271 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5271 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5258 80 96))) (concat (mux (sgt v_5277 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5277 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5258 112 128))) (concat (mux (sgt v_5284 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5284 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5283 16 32))) (concat (mux (sgt v_5290 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5290 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5283 48 64))) (concat (mux (sgt v_5296 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5296 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5283 80 96))) (mux (sgt v_5302 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5302 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5283 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3133 : Mem) (v_3134 : reg (bv 128)) => do
      v_9205 <- evaluateAddress v_3133;
      v_9206 <- load v_9205 16;
      v_9207 <- eval (extract v_9206 0 32);
      v_9213 <- eval (extract v_9206 32 64);
      v_9219 <- eval (extract v_9206 64 96);
      v_9225 <- eval (extract v_9206 96 128);
      v_9231 <- getRegister v_3134;
      v_9232 <- eval (extract v_9231 0 32);
      v_9238 <- eval (extract v_9231 32 64);
      v_9244 <- eval (extract v_9231 64 96);
      v_9250 <- eval (extract v_9231 96 128);
      setRegister (lhs.of_reg v_3134) (concat (mux (sgt v_9207 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9207 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9206 16 32))) (concat (mux (sgt v_9213 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9213 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9206 48 64))) (concat (mux (sgt v_9219 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9219 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9206 80 96))) (concat (mux (sgt v_9225 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9225 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9206 112 128))) (concat (mux (sgt v_9232 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9232 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9231 16 32))) (concat (mux (sgt v_9238 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9238 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9231 48 64))) (concat (mux (sgt v_9244 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9244 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9231 80 96))) (mux (sgt v_9250 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9250 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9231 112 128))))))))));
      pure ()
    pat_end
