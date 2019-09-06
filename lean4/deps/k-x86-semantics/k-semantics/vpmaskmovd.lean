def vpmaskmovd1 : instruction :=
  definst "vpmaskmovd" $ do
    pattern fun (v_3482 : Mem) (v_3483 : reg (bv 128)) (v_3484 : reg (bv 128)) => do
      v_18681 <- getRegister v_3483;
      v_18683 <- evaluateAddress v_3482;
      v_18684 <- load v_18683 16;
      setRegister (lhs.of_reg v_3484) (concat (mux (isBitSet v_18681 0) (extract v_18684 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18681 32) (extract v_18684 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18681 64) (extract v_18684 64 96) (expression.bv_nat 32 0)) (mux (isBitSet v_18681 96) (extract v_18684 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3487 : Mem) (v_3488 : reg (bv 256)) (v_3489 : reg (bv 256)) => do
      v_18700 <- getRegister v_3488;
      v_18702 <- evaluateAddress v_3487;
      v_18703 <- load v_18702 32;
      setRegister (lhs.of_reg v_3489) (concat (mux (isBitSet v_18700 0) (extract v_18703 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18700 32) (extract v_18703 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18700 64) (extract v_18703 64 96) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18700 96) (extract v_18703 96 128) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18700 128) (extract v_18703 128 160) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18700 160) (extract v_18703 160 192) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18700 192) (extract v_18703 192 224) (expression.bv_nat 32 0)) (mux (isBitSet v_18700 224) (extract v_18703 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_3473 : reg (bv 128)) (v_3474 : reg (bv 128)) (v_3472 : Mem) => do
      v_19245 <- evaluateAddress v_3472;
      v_19246 <- getRegister v_3474;
      v_19248 <- getRegister v_3473;
      v_19250 <- load v_19245 16;
      store v_19245 (concat (mux (isBitSet v_19246 0) (extract v_19248 0 32) (extract v_19250 0 32)) (concat (mux (isBitSet v_19246 32) (extract v_19248 32 64) (extract v_19250 32 64)) (concat (mux (isBitSet v_19246 64) (extract v_19248 64 96) (extract v_19250 64 96)) (mux (isBitSet v_19246 96) (extract v_19248 96 128) (extract v_19250 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3478 : reg (bv 256)) (v_3479 : reg (bv 256)) (v_3477 : Mem) => do
      v_19269 <- evaluateAddress v_3477;
      v_19270 <- getRegister v_3479;
      v_19272 <- getRegister v_3478;
      v_19274 <- load v_19269 32;
      store v_19269 (concat (mux (isBitSet v_19270 0) (extract v_19272 0 32) (extract v_19274 0 32)) (concat (mux (isBitSet v_19270 32) (extract v_19272 32 64) (extract v_19274 32 64)) (concat (mux (isBitSet v_19270 64) (extract v_19272 64 96) (extract v_19274 64 96)) (concat (mux (isBitSet v_19270 96) (extract v_19272 96 128) (extract v_19274 96 128)) (concat (mux (isBitSet v_19270 128) (extract v_19272 128 160) (extract v_19274 128 160)) (concat (mux (isBitSet v_19270 160) (extract v_19272 160 192) (extract v_19274 160 192)) (concat (mux (isBitSet v_19270 192) (extract v_19272 192 224) (extract v_19274 192 224)) (mux (isBitSet v_19270 224) (extract v_19272 224 256) (extract v_19274 224 256))))))))) 32;
      pure ()
    pat_end
