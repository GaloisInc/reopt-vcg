def vpmaskmovq1 : instruction :=
  definst "vpmaskmovq" $ do
    pattern fun (v_3475 : Mem) (v_3476 : reg (bv 128)) (v_3477 : reg (bv 128)) => do
      v_18710 <- getRegister v_3476;
      v_18712 <- evaluateAddress v_3475;
      v_18713 <- load v_18712 16;
      setRegister (lhs.of_reg v_3477) (concat (mux (isBitSet v_18710 0) (extract v_18713 0 64) (expression.bv_nat 64 0)) (mux (isBitSet v_18710 64) (extract v_18713 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3480 : Mem) (v_3481 : reg (bv 256)) (v_3482 : reg (bv 256)) => do
      v_18721 <- getRegister v_3481;
      v_18723 <- evaluateAddress v_3480;
      v_18724 <- load v_18723 32;
      setRegister (lhs.of_reg v_3482) (concat (mux (isBitSet v_18721 0) (extract v_18724 0 64) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_18721 64) (extract v_18724 64 128) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_18721 128) (extract v_18724 128 192) (expression.bv_nat 64 0)) (mux (isBitSet v_18721 192) (extract v_18724 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_3466 : reg (bv 128)) (v_3467 : reg (bv 128)) (v_3465 : Mem) => do
      v_19286 <- evaluateAddress v_3465;
      v_19287 <- getRegister v_3467;
      v_19289 <- getRegister v_3466;
      v_19291 <- load v_19286 16;
      store v_19286 (concat (mux (isBitSet v_19287 0) (extract v_19289 0 64) (extract v_19291 0 64)) (mux (isBitSet v_19287 64) (extract v_19289 64 128) (extract v_19291 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_3471 : reg (bv 256)) (v_3472 : reg (bv 256)) (v_3470 : Mem) => do
      v_19300 <- evaluateAddress v_3470;
      v_19301 <- getRegister v_3472;
      v_19303 <- getRegister v_3471;
      v_19305 <- load v_19300 32;
      store v_19300 (concat (mux (isBitSet v_19301 0) (extract v_19303 0 64) (extract v_19305 0 64)) (concat (mux (isBitSet v_19301 64) (extract v_19303 64 128) (extract v_19305 64 128)) (concat (mux (isBitSet v_19301 128) (extract v_19303 128 192) (extract v_19305 128 192)) (mux (isBitSet v_19301 192) (extract v_19303 192 256) (extract v_19305 192 256))))) 32;
      pure ()
    pat_end
