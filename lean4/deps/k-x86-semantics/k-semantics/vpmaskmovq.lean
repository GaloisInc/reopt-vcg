def vpmaskmovq1 : instruction :=
  definst "vpmaskmovq" $ do
    pattern fun (v_3502 : Mem) (v_3503 : reg (bv 128)) (v_3504 : reg (bv 128)) => do
      v_18737 <- getRegister v_3503;
      v_18739 <- evaluateAddress v_3502;
      v_18740 <- load v_18739 16;
      setRegister (lhs.of_reg v_3504) (concat (mux (isBitSet v_18737 0) (extract v_18740 0 64) (expression.bv_nat 64 0)) (mux (isBitSet v_18737 64) (extract v_18740 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3507 : Mem) (v_3508 : reg (bv 256)) (v_3509 : reg (bv 256)) => do
      v_18748 <- getRegister v_3508;
      v_18750 <- evaluateAddress v_3507;
      v_18751 <- load v_18750 32;
      setRegister (lhs.of_reg v_3509) (concat (mux (isBitSet v_18748 0) (extract v_18751 0 64) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_18748 64) (extract v_18751 64 128) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_18748 128) (extract v_18751 128 192) (expression.bv_nat 64 0)) (mux (isBitSet v_18748 192) (extract v_18751 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_3493 : reg (bv 128)) (v_3494 : reg (bv 128)) (v_3492 : Mem) => do
      v_19313 <- evaluateAddress v_3492;
      v_19314 <- getRegister v_3494;
      v_19316 <- getRegister v_3493;
      v_19318 <- load v_19313 16;
      store v_19313 (concat (mux (isBitSet v_19314 0) (extract v_19316 0 64) (extract v_19318 0 64)) (mux (isBitSet v_19314 64) (extract v_19316 64 128) (extract v_19318 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_3498 : reg (bv 256)) (v_3499 : reg (bv 256)) (v_3497 : Mem) => do
      v_19327 <- evaluateAddress v_3497;
      v_19328 <- getRegister v_3499;
      v_19330 <- getRegister v_3498;
      v_19332 <- load v_19327 32;
      store v_19327 (concat (mux (isBitSet v_19328 0) (extract v_19330 0 64) (extract v_19332 0 64)) (concat (mux (isBitSet v_19328 64) (extract v_19330 64 128) (extract v_19332 64 128)) (concat (mux (isBitSet v_19328 128) (extract v_19330 128 192) (extract v_19332 128 192)) (mux (isBitSet v_19328 192) (extract v_19330 192 256) (extract v_19332 192 256))))) 32;
      pure ()
    pat_end
