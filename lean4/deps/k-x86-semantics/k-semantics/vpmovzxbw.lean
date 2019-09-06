def vpmovzxbw1 : instruction :=
  definst "vpmovzxbw" $ do
    pattern fun (v_2827 : reg (bv 128)) (v_2828 : reg (bv 128)) => do
      v_5827 <- getRegister v_2827;
      setRegister (lhs.of_reg v_2828) (concat (expression.bv_nat 8 0) (concat (extract v_5827 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5827 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5827 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5827 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5827 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5827 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5827 112 120) (concat (expression.bv_nat 8 0) (extract v_5827 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2837 : reg (bv 128)) (v_2836 : reg (bv 256)) => do
      v_5856 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2836) (concat (expression.bv_nat 8 0) (concat (extract v_5856 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_5856 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_5856 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_5856 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_5856 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_5856 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_5856 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_5856 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_5856 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5856 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5856 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5856 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5856 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5856 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5856 112 120) (concat (expression.bv_nat 8 0) (extract v_5856 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2822 : Mem) (v_2823 : reg (bv 128)) => do
      v_12210 <- evaluateAddress v_2822;
      v_12211 <- load v_12210 8;
      setRegister (lhs.of_reg v_2823) (concat (expression.bv_nat 8 0) (concat (extract v_12211 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12211 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12211 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12211 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12211 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12211 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12211 48 56) (concat (expression.bv_nat 8 0) (extract v_12211 56 64))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2831 : Mem) (v_2832 : reg (bv 256)) => do
      v_12236 <- evaluateAddress v_2831;
      v_12237 <- load v_12236 16;
      setRegister (lhs.of_reg v_2832) (concat (expression.bv_nat 8 0) (concat (extract v_12237 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12237 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12237 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12237 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12237 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12237 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12237 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_12237 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_12237 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_12237 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_12237 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_12237 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_12237 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_12237 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_12237 112 120) (concat (expression.bv_nat 8 0) (extract v_12237 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end
