def vpmaskmovd1 : instruction :=
  definst "vpmaskmovd" $ do
    pattern fun (v_3455 : Mem) (v_3456 : reg (bv 128)) (v_3457 : reg (bv 128)) => do
      v_18654 <- getRegister v_3456;
      v_18656 <- evaluateAddress v_3455;
      v_18657 <- load v_18656 16;
      setRegister (lhs.of_reg v_3457) (concat (mux (isBitSet v_18654 0) (extract v_18657 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18654 32) (extract v_18657 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18654 64) (extract v_18657 64 96) (expression.bv_nat 32 0)) (mux (isBitSet v_18654 96) (extract v_18657 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3460 : Mem) (v_3461 : reg (bv 256)) (v_3462 : reg (bv 256)) => do
      v_18673 <- getRegister v_3461;
      v_18675 <- evaluateAddress v_3460;
      v_18676 <- load v_18675 32;
      setRegister (lhs.of_reg v_3462) (concat (mux (isBitSet v_18673 0) (extract v_18676 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18673 32) (extract v_18676 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18673 64) (extract v_18676 64 96) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18673 96) (extract v_18676 96 128) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18673 128) (extract v_18676 128 160) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18673 160) (extract v_18676 160 192) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_18673 192) (extract v_18676 192 224) (expression.bv_nat 32 0)) (mux (isBitSet v_18673 224) (extract v_18676 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_3446 : reg (bv 128)) (v_3447 : reg (bv 128)) (v_3445 : Mem) => do
      v_19218 <- evaluateAddress v_3445;
      v_19219 <- getRegister v_3447;
      v_19221 <- getRegister v_3446;
      v_19223 <- load v_19218 16;
      store v_19218 (concat (mux (isBitSet v_19219 0) (extract v_19221 0 32) (extract v_19223 0 32)) (concat (mux (isBitSet v_19219 32) (extract v_19221 32 64) (extract v_19223 32 64)) (concat (mux (isBitSet v_19219 64) (extract v_19221 64 96) (extract v_19223 64 96)) (mux (isBitSet v_19219 96) (extract v_19221 96 128) (extract v_19223 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3451 : reg (bv 256)) (v_3452 : reg (bv 256)) (v_3450 : Mem) => do
      v_19242 <- evaluateAddress v_3450;
      v_19243 <- getRegister v_3452;
      v_19245 <- getRegister v_3451;
      v_19247 <- load v_19242 32;
      store v_19242 (concat (mux (isBitSet v_19243 0) (extract v_19245 0 32) (extract v_19247 0 32)) (concat (mux (isBitSet v_19243 32) (extract v_19245 32 64) (extract v_19247 32 64)) (concat (mux (isBitSet v_19243 64) (extract v_19245 64 96) (extract v_19247 64 96)) (concat (mux (isBitSet v_19243 96) (extract v_19245 96 128) (extract v_19247 96 128)) (concat (mux (isBitSet v_19243 128) (extract v_19245 128 160) (extract v_19247 128 160)) (concat (mux (isBitSet v_19243 160) (extract v_19245 160 192) (extract v_19247 160 192)) (concat (mux (isBitSet v_19243 192) (extract v_19245 192 224) (extract v_19247 192 224)) (mux (isBitSet v_19243 224) (extract v_19245 224 256) (extract v_19247 224 256))))))))) 32;
      pure ()
    pat_end
