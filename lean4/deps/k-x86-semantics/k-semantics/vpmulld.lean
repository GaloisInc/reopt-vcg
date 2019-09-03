def vpmulld1 : instruction :=
  definst "vpmulld" $ do
    pattern fun (v_2896 : reg (bv 128)) (v_2897 : reg (bv 128)) (v_2898 : reg (bv 128)) => do
      v_6739 <- getRegister v_2897;
      v_6743 <- getRegister v_2896;
      setRegister (lhs.of_reg v_2898) (concat (extract (mul (mi 64 (svalueMInt (extract v_6739 0 32))) (mi 64 (svalueMInt (extract v_6743 0 32)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6739 32 64))) (mi 64 (svalueMInt (extract v_6743 32 64)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6739 64 96))) (mi 64 (svalueMInt (extract v_6743 64 96)))) 32 64) (extract (mul (mi 64 (svalueMInt (extract v_6739 96 128))) (mi 64 (svalueMInt (extract v_6743 96 128)))) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2907 : reg (bv 256)) (v_2908 : reg (bv 256)) (v_2909 : reg (bv 256)) => do
      v_6782 <- getRegister v_2908;
      v_6786 <- getRegister v_2907;
      setRegister (lhs.of_reg v_2909) (concat (extract (mul (mi 64 (svalueMInt (extract v_6782 0 32))) (mi 64 (svalueMInt (extract v_6786 0 32)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6782 32 64))) (mi 64 (svalueMInt (extract v_6786 32 64)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6782 64 96))) (mi 64 (svalueMInt (extract v_6786 64 96)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6782 96 128))) (mi 64 (svalueMInt (extract v_6786 96 128)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6782 128 160))) (mi 64 (svalueMInt (extract v_6786 128 160)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6782 160 192))) (mi 64 (svalueMInt (extract v_6786 160 192)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_6782 192 224))) (mi 64 (svalueMInt (extract v_6786 192 224)))) 32 64) (extract (mul (mi 64 (svalueMInt (extract v_6782 224 256))) (mi 64 (svalueMInt (extract v_6786 224 256)))) 32 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2893 : Mem) (v_2891 : reg (bv 128)) (v_2892 : reg (bv 128)) => do
      v_13812 <- getRegister v_2891;
      v_13816 <- evaluateAddress v_2893;
      v_13817 <- load v_13816 16;
      setRegister (lhs.of_reg v_2892) (concat (extract (mul (mi 64 (svalueMInt (extract v_13812 0 32))) (mi 64 (svalueMInt (extract v_13817 0 32)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13812 32 64))) (mi 64 (svalueMInt (extract v_13817 32 64)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13812 64 96))) (mi 64 (svalueMInt (extract v_13817 64 96)))) 32 64) (extract (mul (mi 64 (svalueMInt (extract v_13812 96 128))) (mi 64 (svalueMInt (extract v_13817 96 128)))) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2902 : Mem) (v_2903 : reg (bv 256)) (v_2904 : reg (bv 256)) => do
      v_13851 <- getRegister v_2903;
      v_13855 <- evaluateAddress v_2902;
      v_13856 <- load v_13855 32;
      setRegister (lhs.of_reg v_2904) (concat (extract (mul (mi 64 (svalueMInt (extract v_13851 0 32))) (mi 64 (svalueMInt (extract v_13856 0 32)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13851 32 64))) (mi 64 (svalueMInt (extract v_13856 32 64)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13851 64 96))) (mi 64 (svalueMInt (extract v_13856 64 96)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13851 96 128))) (mi 64 (svalueMInt (extract v_13856 96 128)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13851 128 160))) (mi 64 (svalueMInt (extract v_13856 128 160)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13851 160 192))) (mi 64 (svalueMInt (extract v_13856 160 192)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13851 192 224))) (mi 64 (svalueMInt (extract v_13856 192 224)))) 32 64) (extract (mul (mi 64 (svalueMInt (extract v_13851 224 256))) (mi 64 (svalueMInt (extract v_13856 224 256)))) 32 64))))))));
      pure ()
    pat_end
