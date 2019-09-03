def vpmaskmovd1 : instruction :=
  definst "vpmaskmovd" $ do
    pattern fun (v_3391 : Mem) (v_3392 : reg (bv 128)) (v_3393 : reg (bv 128)) => do
      v_19818 <- getRegister v_3392;
      v_19821 <- evaluateAddress v_3391;
      v_19822 <- load v_19821 16;
      setRegister (lhs.of_reg v_3393) (concat (mux (eq (extract v_19818 0 1) (expression.bv_nat 1 1)) (extract v_19822 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19818 32 33) (expression.bv_nat 1 1)) (extract v_19822 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19818 64 65) (expression.bv_nat 1 1)) (extract v_19822 64 96) (expression.bv_nat 32 0)) (mux (eq (extract v_19818 96 97) (expression.bv_nat 1 1)) (extract v_19822 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3396 : Mem) (v_3397 : reg (bv 256)) (v_3398 : reg (bv 256)) => do
      v_19841 <- getRegister v_3397;
      v_19844 <- evaluateAddress v_3396;
      v_19845 <- load v_19844 32;
      setRegister (lhs.of_reg v_3398) (concat (mux (eq (extract v_19841 0 1) (expression.bv_nat 1 1)) (extract v_19845 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19841 32 33) (expression.bv_nat 1 1)) (extract v_19845 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19841 64 65) (expression.bv_nat 1 1)) (extract v_19845 64 96) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19841 96 97) (expression.bv_nat 1 1)) (extract v_19845 96 128) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19841 128 129) (expression.bv_nat 1 1)) (extract v_19845 128 160) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19841 160 161) (expression.bv_nat 1 1)) (extract v_19845 160 192) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19841 192 193) (expression.bv_nat 1 1)) (extract v_19845 192 224) (expression.bv_nat 32 0)) (mux (eq (extract v_19841 224 225) (expression.bv_nat 1 1)) (extract v_19845 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_3382 : reg (bv 128)) (v_3383 : reg (bv 128)) (v_3381 : Mem) => do
      v_20408 <- evaluateAddress v_3381;
      v_20409 <- getRegister v_3383;
      v_20412 <- getRegister v_3382;
      v_20414 <- load v_20408 16;
      store v_20408 (concat (mux (eq (extract v_20409 0 1) (expression.bv_nat 1 1)) (extract v_20412 0 32) (extract v_20414 0 32)) (concat (mux (eq (extract v_20409 32 33) (expression.bv_nat 1 1)) (extract v_20412 32 64) (extract v_20414 32 64)) (concat (mux (eq (extract v_20409 64 65) (expression.bv_nat 1 1)) (extract v_20412 64 96) (extract v_20414 64 96)) (mux (eq (extract v_20409 96 97) (expression.bv_nat 1 1)) (extract v_20412 96 128) (extract v_20414 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3387 : reg (bv 256)) (v_3388 : reg (bv 256)) (v_3386 : Mem) => do
      v_20436 <- evaluateAddress v_3386;
      v_20437 <- getRegister v_3388;
      v_20440 <- getRegister v_3387;
      v_20442 <- load v_20436 32;
      store v_20436 (concat (mux (eq (extract v_20437 0 1) (expression.bv_nat 1 1)) (extract v_20440 0 32) (extract v_20442 0 32)) (concat (mux (eq (extract v_20437 32 33) (expression.bv_nat 1 1)) (extract v_20440 32 64) (extract v_20442 32 64)) (concat (mux (eq (extract v_20437 64 65) (expression.bv_nat 1 1)) (extract v_20440 64 96) (extract v_20442 64 96)) (concat (mux (eq (extract v_20437 96 97) (expression.bv_nat 1 1)) (extract v_20440 96 128) (extract v_20442 96 128)) (concat (mux (eq (extract v_20437 128 129) (expression.bv_nat 1 1)) (extract v_20440 128 160) (extract v_20442 128 160)) (concat (mux (eq (extract v_20437 160 161) (expression.bv_nat 1 1)) (extract v_20440 160 192) (extract v_20442 160 192)) (concat (mux (eq (extract v_20437 192 193) (expression.bv_nat 1 1)) (extract v_20440 192 224) (extract v_20442 192 224)) (mux (eq (extract v_20437 224 225) (expression.bv_nat 1 1)) (extract v_20440 224 256) (extract v_20442 224 256))))))))) 32;
      pure ()
    pat_end
