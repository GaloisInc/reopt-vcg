def vpaddusw1 : instruction :=
  definst "vpaddusw" $ do
    pattern fun (v_2542 : reg (bv 128)) (v_2543 : reg (bv 128)) (v_2544 : reg (bv 128)) => do
      v_5356 <- getRegister v_2543;
      v_5359 <- getRegister v_2542;
      v_5362 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 0 16)) (concat (expression.bv_nat 1 0) (extract v_5359 0 16)));
      v_5370 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 16 32)) (concat (expression.bv_nat 1 0) (extract v_5359 16 32)));
      v_5378 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 32 48)) (concat (expression.bv_nat 1 0) (extract v_5359 32 48)));
      v_5386 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 48 64)) (concat (expression.bv_nat 1 0) (extract v_5359 48 64)));
      v_5394 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 64 80)) (concat (expression.bv_nat 1 0) (extract v_5359 64 80)));
      v_5402 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 80 96)) (concat (expression.bv_nat 1 0) (extract v_5359 80 96)));
      v_5410 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 96 112)) (concat (expression.bv_nat 1 0) (extract v_5359 96 112)));
      v_5418 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5356 112 128)) (concat (expression.bv_nat 1 0) (extract v_5359 112 128)));
      setRegister (lhs.of_reg v_2544) (concat (mux (isBitSet v_5362 0) (expression.bv_nat 16 65535) (extract v_5362 1 17)) (concat (mux (isBitSet v_5370 0) (expression.bv_nat 16 65535) (extract v_5370 1 17)) (concat (mux (isBitSet v_5378 0) (expression.bv_nat 16 65535) (extract v_5378 1 17)) (concat (mux (isBitSet v_5386 0) (expression.bv_nat 16 65535) (extract v_5386 1 17)) (concat (mux (isBitSet v_5394 0) (expression.bv_nat 16 65535) (extract v_5394 1 17)) (concat (mux (isBitSet v_5402 0) (expression.bv_nat 16 65535) (extract v_5402 1 17)) (concat (mux (isBitSet v_5410 0) (expression.bv_nat 16 65535) (extract v_5410 1 17)) (mux (isBitSet v_5418 0) (expression.bv_nat 16 65535) (extract v_5418 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2553 : reg (bv 256)) (v_2554 : reg (bv 256)) (v_2555 : reg (bv 256)) => do
      v_5435 <- getRegister v_2554;
      v_5438 <- getRegister v_2553;
      v_5441 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 0 16)) (concat (expression.bv_nat 1 0) (extract v_5438 0 16)));
      v_5449 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 16 32)) (concat (expression.bv_nat 1 0) (extract v_5438 16 32)));
      v_5457 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 32 48)) (concat (expression.bv_nat 1 0) (extract v_5438 32 48)));
      v_5465 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 48 64)) (concat (expression.bv_nat 1 0) (extract v_5438 48 64)));
      v_5473 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 64 80)) (concat (expression.bv_nat 1 0) (extract v_5438 64 80)));
      v_5481 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 80 96)) (concat (expression.bv_nat 1 0) (extract v_5438 80 96)));
      v_5489 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 96 112)) (concat (expression.bv_nat 1 0) (extract v_5438 96 112)));
      v_5497 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 112 128)) (concat (expression.bv_nat 1 0) (extract v_5438 112 128)));
      v_5505 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 128 144)) (concat (expression.bv_nat 1 0) (extract v_5438 128 144)));
      v_5513 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 144 160)) (concat (expression.bv_nat 1 0) (extract v_5438 144 160)));
      v_5521 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 160 176)) (concat (expression.bv_nat 1 0) (extract v_5438 160 176)));
      v_5529 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 176 192)) (concat (expression.bv_nat 1 0) (extract v_5438 176 192)));
      v_5537 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 192 208)) (concat (expression.bv_nat 1 0) (extract v_5438 192 208)));
      v_5545 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 208 224)) (concat (expression.bv_nat 1 0) (extract v_5438 208 224)));
      v_5553 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 224 240)) (concat (expression.bv_nat 1 0) (extract v_5438 224 240)));
      v_5561 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5435 240 256)) (concat (expression.bv_nat 1 0) (extract v_5438 240 256)));
      setRegister (lhs.of_reg v_2555) (concat (mux (isBitSet v_5441 0) (expression.bv_nat 16 65535) (extract v_5441 1 17)) (concat (mux (isBitSet v_5449 0) (expression.bv_nat 16 65535) (extract v_5449 1 17)) (concat (mux (isBitSet v_5457 0) (expression.bv_nat 16 65535) (extract v_5457 1 17)) (concat (mux (isBitSet v_5465 0) (expression.bv_nat 16 65535) (extract v_5465 1 17)) (concat (mux (isBitSet v_5473 0) (expression.bv_nat 16 65535) (extract v_5473 1 17)) (concat (mux (isBitSet v_5481 0) (expression.bv_nat 16 65535) (extract v_5481 1 17)) (concat (mux (isBitSet v_5489 0) (expression.bv_nat 16 65535) (extract v_5489 1 17)) (concat (mux (isBitSet v_5497 0) (expression.bv_nat 16 65535) (extract v_5497 1 17)) (concat (mux (isBitSet v_5505 0) (expression.bv_nat 16 65535) (extract v_5505 1 17)) (concat (mux (isBitSet v_5513 0) (expression.bv_nat 16 65535) (extract v_5513 1 17)) (concat (mux (isBitSet v_5521 0) (expression.bv_nat 16 65535) (extract v_5521 1 17)) (concat (mux (isBitSet v_5529 0) (expression.bv_nat 16 65535) (extract v_5529 1 17)) (concat (mux (isBitSet v_5537 0) (expression.bv_nat 16 65535) (extract v_5537 1 17)) (concat (mux (isBitSet v_5545 0) (expression.bv_nat 16 65535) (extract v_5545 1 17)) (concat (mux (isBitSet v_5553 0) (expression.bv_nat 16 65535) (extract v_5553 1 17)) (mux (isBitSet v_5561 0) (expression.bv_nat 16 65535) (extract v_5561 1 17)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2537 : Mem) (v_2538 : reg (bv 128)) (v_2539 : reg (bv 128)) => do
      v_14092 <- getRegister v_2538;
      v_14095 <- evaluateAddress v_2537;
      v_14096 <- load v_14095 16;
      v_14099 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 0 16)) (concat (expression.bv_nat 1 0) (extract v_14096 0 16)));
      v_14107 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 16 32)) (concat (expression.bv_nat 1 0) (extract v_14096 16 32)));
      v_14115 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 32 48)) (concat (expression.bv_nat 1 0) (extract v_14096 32 48)));
      v_14123 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 48 64)) (concat (expression.bv_nat 1 0) (extract v_14096 48 64)));
      v_14131 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 64 80)) (concat (expression.bv_nat 1 0) (extract v_14096 64 80)));
      v_14139 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 80 96)) (concat (expression.bv_nat 1 0) (extract v_14096 80 96)));
      v_14147 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 96 112)) (concat (expression.bv_nat 1 0) (extract v_14096 96 112)));
      v_14155 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14092 112 128)) (concat (expression.bv_nat 1 0) (extract v_14096 112 128)));
      setRegister (lhs.of_reg v_2539) (concat (mux (isBitSet v_14099 0) (expression.bv_nat 16 65535) (extract v_14099 1 17)) (concat (mux (isBitSet v_14107 0) (expression.bv_nat 16 65535) (extract v_14107 1 17)) (concat (mux (isBitSet v_14115 0) (expression.bv_nat 16 65535) (extract v_14115 1 17)) (concat (mux (isBitSet v_14123 0) (expression.bv_nat 16 65535) (extract v_14123 1 17)) (concat (mux (isBitSet v_14131 0) (expression.bv_nat 16 65535) (extract v_14131 1 17)) (concat (mux (isBitSet v_14139 0) (expression.bv_nat 16 65535) (extract v_14139 1 17)) (concat (mux (isBitSet v_14147 0) (expression.bv_nat 16 65535) (extract v_14147 1 17)) (mux (isBitSet v_14155 0) (expression.bv_nat 16 65535) (extract v_14155 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2548 : Mem) (v_2549 : reg (bv 256)) (v_2550 : reg (bv 256)) => do
      v_14167 <- getRegister v_2549;
      v_14170 <- evaluateAddress v_2548;
      v_14171 <- load v_14170 32;
      v_14174 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 0 16)) (concat (expression.bv_nat 1 0) (extract v_14171 0 16)));
      v_14182 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 16 32)) (concat (expression.bv_nat 1 0) (extract v_14171 16 32)));
      v_14190 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 32 48)) (concat (expression.bv_nat 1 0) (extract v_14171 32 48)));
      v_14198 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 48 64)) (concat (expression.bv_nat 1 0) (extract v_14171 48 64)));
      v_14206 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 64 80)) (concat (expression.bv_nat 1 0) (extract v_14171 64 80)));
      v_14214 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 80 96)) (concat (expression.bv_nat 1 0) (extract v_14171 80 96)));
      v_14222 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 96 112)) (concat (expression.bv_nat 1 0) (extract v_14171 96 112)));
      v_14230 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 112 128)) (concat (expression.bv_nat 1 0) (extract v_14171 112 128)));
      v_14238 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 128 144)) (concat (expression.bv_nat 1 0) (extract v_14171 128 144)));
      v_14246 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 144 160)) (concat (expression.bv_nat 1 0) (extract v_14171 144 160)));
      v_14254 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 160 176)) (concat (expression.bv_nat 1 0) (extract v_14171 160 176)));
      v_14262 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 176 192)) (concat (expression.bv_nat 1 0) (extract v_14171 176 192)));
      v_14270 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 192 208)) (concat (expression.bv_nat 1 0) (extract v_14171 192 208)));
      v_14278 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 208 224)) (concat (expression.bv_nat 1 0) (extract v_14171 208 224)));
      v_14286 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 224 240)) (concat (expression.bv_nat 1 0) (extract v_14171 224 240)));
      v_14294 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14167 240 256)) (concat (expression.bv_nat 1 0) (extract v_14171 240 256)));
      setRegister (lhs.of_reg v_2550) (concat (mux (isBitSet v_14174 0) (expression.bv_nat 16 65535) (extract v_14174 1 17)) (concat (mux (isBitSet v_14182 0) (expression.bv_nat 16 65535) (extract v_14182 1 17)) (concat (mux (isBitSet v_14190 0) (expression.bv_nat 16 65535) (extract v_14190 1 17)) (concat (mux (isBitSet v_14198 0) (expression.bv_nat 16 65535) (extract v_14198 1 17)) (concat (mux (isBitSet v_14206 0) (expression.bv_nat 16 65535) (extract v_14206 1 17)) (concat (mux (isBitSet v_14214 0) (expression.bv_nat 16 65535) (extract v_14214 1 17)) (concat (mux (isBitSet v_14222 0) (expression.bv_nat 16 65535) (extract v_14222 1 17)) (concat (mux (isBitSet v_14230 0) (expression.bv_nat 16 65535) (extract v_14230 1 17)) (concat (mux (isBitSet v_14238 0) (expression.bv_nat 16 65535) (extract v_14238 1 17)) (concat (mux (isBitSet v_14246 0) (expression.bv_nat 16 65535) (extract v_14246 1 17)) (concat (mux (isBitSet v_14254 0) (expression.bv_nat 16 65535) (extract v_14254 1 17)) (concat (mux (isBitSet v_14262 0) (expression.bv_nat 16 65535) (extract v_14262 1 17)) (concat (mux (isBitSet v_14270 0) (expression.bv_nat 16 65535) (extract v_14270 1 17)) (concat (mux (isBitSet v_14278 0) (expression.bv_nat 16 65535) (extract v_14278 1 17)) (concat (mux (isBitSet v_14286 0) (expression.bv_nat 16 65535) (extract v_14286 1 17)) (mux (isBitSet v_14294 0) (expression.bv_nat 16 65535) (extract v_14294 1 17)))))))))))))))));
      pure ()
    pat_end
