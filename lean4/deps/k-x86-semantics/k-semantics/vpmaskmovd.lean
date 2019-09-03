def vpmaskmovd1 : instruction :=
  definst "vpmaskmovd" $ do
    pattern fun (v_3406 : Mem) (v_3402 : reg (bv 128)) (v_3403 : reg (bv 128)) => do
      v_19093 <- getRegister v_3402;
      v_19096 <- evaluateAddress v_3406;
      v_19097 <- load v_19096 16;
      setRegister (lhs.of_reg v_3403) (concat (mux (eq (extract v_19093 0 1) (expression.bv_nat 1 1)) (extract v_19097 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19093 32 33) (expression.bv_nat 1 1)) (extract v_19097 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19093 64 65) (expression.bv_nat 1 1)) (extract v_19097 64 96) (expression.bv_nat 32 0)) (mux (eq (extract v_19093 96 97) (expression.bv_nat 1 1)) (extract v_19097 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3409 : Mem) (v_3410 : reg (bv 256)) (v_3411 : reg (bv 256)) => do
      v_19116 <- getRegister v_3410;
      v_19119 <- evaluateAddress v_3409;
      v_19120 <- load v_19119 32;
      setRegister (lhs.of_reg v_3411) (concat (mux (eq (extract v_19116 0 1) (expression.bv_nat 1 1)) (extract v_19120 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19116 32 33) (expression.bv_nat 1 1)) (extract v_19120 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19116 64 65) (expression.bv_nat 1 1)) (extract v_19120 64 96) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19116 96 97) (expression.bv_nat 1 1)) (extract v_19120 96 128) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19116 128 129) (expression.bv_nat 1 1)) (extract v_19120 128 160) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19116 160 161) (expression.bv_nat 1 1)) (extract v_19120 160 192) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_19116 192 193) (expression.bv_nat 1 1)) (extract v_19120 192 224) (expression.bv_nat 32 0)) (mux (eq (extract v_19116 224 225) (expression.bv_nat 1 1)) (extract v_19120 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_3392 : reg (bv 128)) (v_3393 : reg (bv 128)) (v_3396 : Mem) => do
      v_19679 <- evaluateAddress v_3396;
      v_19680 <- getRegister v_3393;
      v_19683 <- getRegister v_3392;
      v_19685 <- load v_19679 16;
      store v_19679 (concat (mux (eq (extract v_19680 0 1) (expression.bv_nat 1 1)) (extract v_19683 0 32) (extract v_19685 0 32)) (concat (mux (eq (extract v_19680 32 33) (expression.bv_nat 1 1)) (extract v_19683 32 64) (extract v_19685 32 64)) (concat (mux (eq (extract v_19680 64 65) (expression.bv_nat 1 1)) (extract v_19683 64 96) (extract v_19685 64 96)) (mux (eq (extract v_19680 96 97) (expression.bv_nat 1 1)) (extract v_19683 96 128) (extract v_19685 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_3400 : reg (bv 256)) (v_3401 : reg (bv 256)) (v_3399 : Mem) => do
      v_19707 <- evaluateAddress v_3399;
      v_19708 <- getRegister v_3401;
      v_19711 <- getRegister v_3400;
      v_19713 <- load v_19707 32;
      store v_19707 (concat (mux (eq (extract v_19708 0 1) (expression.bv_nat 1 1)) (extract v_19711 0 32) (extract v_19713 0 32)) (concat (mux (eq (extract v_19708 32 33) (expression.bv_nat 1 1)) (extract v_19711 32 64) (extract v_19713 32 64)) (concat (mux (eq (extract v_19708 64 65) (expression.bv_nat 1 1)) (extract v_19711 64 96) (extract v_19713 64 96)) (concat (mux (eq (extract v_19708 96 97) (expression.bv_nat 1 1)) (extract v_19711 96 128) (extract v_19713 96 128)) (concat (mux (eq (extract v_19708 128 129) (expression.bv_nat 1 1)) (extract v_19711 128 160) (extract v_19713 128 160)) (concat (mux (eq (extract v_19708 160 161) (expression.bv_nat 1 1)) (extract v_19711 160 192) (extract v_19713 160 192)) (concat (mux (eq (extract v_19708 192 193) (expression.bv_nat 1 1)) (extract v_19711 192 224) (extract v_19713 192 224)) (mux (eq (extract v_19708 224 225) (expression.bv_nat 1 1)) (extract v_19711 224 256) (extract v_19713 224 256))))))))) 32;
      pure ()
    pat_end
