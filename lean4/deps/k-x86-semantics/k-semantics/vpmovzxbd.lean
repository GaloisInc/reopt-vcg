def vpmovzxbd1 : instruction :=
  definst "vpmovzxbd" $ do
    pattern fun (v_2699 : reg (bv 128)) (v_2700 : reg (bv 128)) => do
      v_5728 <- getRegister v_2699;
      setRegister (lhs.of_reg v_2700) (concat (expression.bv_nat 24 0) (concat (extract v_5728 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5728 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5728 112 120) (concat (expression.bv_nat 24 0) (extract v_5728 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2708 : reg (bv 128)) (v_2709 : reg (bv 256)) => do
      v_5745 <- getRegister v_2708;
      setRegister (lhs.of_reg v_2709) (concat (expression.bv_nat 24 0) (concat (extract v_5745 64 72) (concat (expression.bv_nat 24 0) (concat (extract v_5745 72 80) (concat (expression.bv_nat 24 0) (concat (extract v_5745 80 88) (concat (expression.bv_nat 24 0) (concat (extract v_5745 88 96) (concat (expression.bv_nat 24 0) (concat (extract v_5745 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5745 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5745 112 120) (concat (expression.bv_nat 24 0) (extract v_5745 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) (v_2695 : reg (bv 128)) => do
      v_12870 <- evaluateAddress v_2696;
      v_12871 <- load v_12870 4;
      setRegister (lhs.of_reg v_2695) (concat (expression.bv_nat 24 0) (concat (extract v_12871 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12871 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12871 16 24) (concat (expression.bv_nat 24 0) (extract v_12871 24 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2704 : Mem) (v_2705 : reg (bv 256)) => do
      v_12884 <- evaluateAddress v_2704;
      v_12885 <- load v_12884 8;
      setRegister (lhs.of_reg v_2705) (concat (expression.bv_nat 24 0) (concat (extract v_12885 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12885 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12885 16 24) (concat (expression.bv_nat 24 0) (concat (extract v_12885 24 32) (concat (expression.bv_nat 24 0) (concat (extract v_12885 32 40) (concat (expression.bv_nat 24 0) (concat (extract v_12885 40 48) (concat (expression.bv_nat 24 0) (concat (extract v_12885 48 56) (concat (expression.bv_nat 24 0) (extract v_12885 56 64))))))))))))))));
      pure ()
    pat_end
