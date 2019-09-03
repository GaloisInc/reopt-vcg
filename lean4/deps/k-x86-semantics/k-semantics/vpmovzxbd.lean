def vpmovzxbd1 : instruction :=
  definst "vpmovzxbd" $ do
    pattern fun (v_2711 : reg (bv 128)) (v_2712 : reg (bv 128)) => do
      v_5675 <- getRegister v_2711;
      setRegister (lhs.of_reg v_2712) (concat (expression.bv_nat 24 0) (concat (extract v_5675 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5675 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5675 112 120) (concat (expression.bv_nat 24 0) (extract v_5675 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2720 : reg (bv 128)) (v_2722 : reg (bv 256)) => do
      v_5692 <- getRegister v_2720;
      setRegister (lhs.of_reg v_2722) (concat (expression.bv_nat 24 0) (concat (extract v_5692 64 72) (concat (expression.bv_nat 24 0) (concat (extract v_5692 72 80) (concat (expression.bv_nat 24 0) (concat (extract v_5692 80 88) (concat (expression.bv_nat 24 0) (concat (extract v_5692 88 96) (concat (expression.bv_nat 24 0) (concat (extract v_5692 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5692 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5692 112 120) (concat (expression.bv_nat 24 0) (extract v_5692 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2706 : Mem) (v_2707 : reg (bv 128)) => do
      v_12326 <- evaluateAddress v_2706;
      v_12327 <- load v_12326 4;
      setRegister (lhs.of_reg v_2707) (concat (expression.bv_nat 24 0) (concat (extract v_12327 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12327 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12327 16 24) (concat (expression.bv_nat 24 0) (extract v_12327 24 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2715 : Mem) (v_2717 : reg (bv 256)) => do
      v_12340 <- evaluateAddress v_2715;
      v_12341 <- load v_12340 8;
      setRegister (lhs.of_reg v_2717) (concat (expression.bv_nat 24 0) (concat (extract v_12341 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12341 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12341 16 24) (concat (expression.bv_nat 24 0) (concat (extract v_12341 24 32) (concat (expression.bv_nat 24 0) (concat (extract v_12341 32 40) (concat (expression.bv_nat 24 0) (concat (extract v_12341 40 48) (concat (expression.bv_nat 24 0) (concat (extract v_12341 48 56) (concat (expression.bv_nat 24 0) (extract v_12341 56 64))))))))))))))));
      pure ()
    pat_end
