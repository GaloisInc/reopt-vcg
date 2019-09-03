def vpmaskmovq1 : instruction :=
  definst "vpmaskmovq" $ do
    pattern fun (v_3411 : Mem) (v_3412 : reg (bv 128)) (v_3413 : reg (bv 128)) => do
      v_19886 <- getRegister v_3412;
      v_19889 <- evaluateAddress v_3411;
      v_19890 <- load v_19889 16;
      setRegister (lhs.of_reg v_3413) (concat (mux (eq (extract v_19886 0 1) (expression.bv_nat 1 1)) (extract v_19890 0 64) (expression.bv_nat 64 0)) (mux (eq (extract v_19886 64 65) (expression.bv_nat 1 1)) (extract v_19890 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3416 : Mem) (v_3417 : reg (bv 256)) (v_3418 : reg (bv 256)) => do
      v_19899 <- getRegister v_3417;
      v_19902 <- evaluateAddress v_3416;
      v_19903 <- load v_19902 32;
      setRegister (lhs.of_reg v_3418) (concat (mux (eq (extract v_19899 0 1) (expression.bv_nat 1 1)) (extract v_19903 0 64) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_19899 64 65) (expression.bv_nat 1 1)) (extract v_19903 64 128) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_19899 128 129) (expression.bv_nat 1 1)) (extract v_19903 128 192) (expression.bv_nat 64 0)) (mux (eq (extract v_19899 192 193) (expression.bv_nat 1 1)) (extract v_19903 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_3402 : reg (bv 128)) (v_3403 : reg (bv 128)) (v_3401 : Mem) => do
      v_20488 <- evaluateAddress v_3401;
      v_20489 <- getRegister v_3403;
      v_20492 <- getRegister v_3402;
      v_20494 <- load v_20488 16;
      store v_20488 (concat (mux (eq (extract v_20489 0 1) (expression.bv_nat 1 1)) (extract v_20492 0 64) (extract v_20494 0 64)) (mux (eq (extract v_20489 64 65) (expression.bv_nat 1 1)) (extract v_20492 64 128) (extract v_20494 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_3407 : reg (bv 256)) (v_3408 : reg (bv 256)) (v_3406 : Mem) => do
      v_20504 <- evaluateAddress v_3406;
      v_20505 <- getRegister v_3408;
      v_20508 <- getRegister v_3407;
      v_20510 <- load v_20504 32;
      store v_20504 (concat (mux (eq (extract v_20505 0 1) (expression.bv_nat 1 1)) (extract v_20508 0 64) (extract v_20510 0 64)) (concat (mux (eq (extract v_20505 64 65) (expression.bv_nat 1 1)) (extract v_20508 64 128) (extract v_20510 64 128)) (concat (mux (eq (extract v_20505 128 129) (expression.bv_nat 1 1)) (extract v_20508 128 192) (extract v_20510 128 192)) (mux (eq (extract v_20505 192 193) (expression.bv_nat 1 1)) (extract v_20508 192 256) (extract v_20510 192 256))))) 32;
      pure ()
    pat_end
