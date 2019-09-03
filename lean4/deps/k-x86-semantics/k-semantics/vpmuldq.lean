def vpmuldq1 : instruction :=
  definst "vpmuldq" $ do
    pattern fun (v_2808 : reg (bv 128)) (v_2809 : reg (bv 128)) (v_2810 : reg (bv 128)) => do
      v_5987 <- getRegister v_2809;
      v_5991 <- getRegister v_2808;
      setRegister (lhs.of_reg v_2810) (concat (mul (mi 64 (svalueMInt (extract v_5987 32 64))) (mi 64 (svalueMInt (extract v_5991 32 64)))) (mul (mi 64 (svalueMInt (extract v_5987 96 128))) (mi 64 (svalueMInt (extract v_5991 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2819 : reg (bv 256)) (v_2820 : reg (bv 256)) (v_2821 : reg (bv 256)) => do
      v_6010 <- getRegister v_2820;
      v_6014 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2821) (concat (mul (mi 64 (svalueMInt (extract v_6010 32 64))) (mi 64 (svalueMInt (extract v_6014 32 64)))) (concat (mul (mi 64 (svalueMInt (extract v_6010 96 128))) (mi 64 (svalueMInt (extract v_6014 96 128)))) (concat (mul (mi 64 (svalueMInt (extract v_6010 160 192))) (mi 64 (svalueMInt (extract v_6014 160 192)))) (mul (mi 64 (svalueMInt (extract v_6010 224 256))) (mi 64 (svalueMInt (extract v_6014 224 256)))))));
      pure ()
    pat_end;
    pattern fun (v_2805 : Mem) (v_2803 : reg (bv 128)) (v_2804 : reg (bv 128)) => do
      v_13092 <- getRegister v_2803;
      v_13096 <- evaluateAddress v_2805;
      v_13097 <- load v_13096 16;
      setRegister (lhs.of_reg v_2804) (concat (mul (mi 64 (svalueMInt (extract v_13092 32 64))) (mi 64 (svalueMInt (extract v_13097 32 64)))) (mul (mi 64 (svalueMInt (extract v_13092 96 128))) (mi 64 (svalueMInt (extract v_13097 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2814 : Mem) (v_2815 : reg (bv 256)) (v_2816 : reg (bv 256)) => do
      v_13111 <- getRegister v_2815;
      v_13115 <- evaluateAddress v_2814;
      v_13116 <- load v_13115 32;
      setRegister (lhs.of_reg v_2816) (concat (mul (mi 64 (svalueMInt (extract v_13111 32 64))) (mi 64 (svalueMInt (extract v_13116 32 64)))) (concat (mul (mi 64 (svalueMInt (extract v_13111 96 128))) (mi 64 (svalueMInt (extract v_13116 96 128)))) (concat (mul (mi 64 (svalueMInt (extract v_13111 160 192))) (mi 64 (svalueMInt (extract v_13116 160 192)))) (mul (mi 64 (svalueMInt (extract v_13111 224 256))) (mi 64 (svalueMInt (extract v_13116 224 256)))))));
      pure ()
    pat_end
