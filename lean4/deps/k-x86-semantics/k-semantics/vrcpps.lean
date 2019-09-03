def vrcpps1 : instruction :=
  definst "vrcpps" $ do
    pattern fun (v_2777 : reg (bv 128)) (v_2778 : reg (bv 128)) => do
      v_6644 <- getRegister v_2777;
      setRegister (lhs.of_reg v_2778) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6644 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6644 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6644 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6644 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2785 : reg (bv 256)) (v_2786 : reg (bv 256)) => do
      v_6669 <- getRegister v_2785;
      setRegister (lhs.of_reg v_2786) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6669 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2772 : Mem) (v_2773 : reg (bv 128)) => do
      v_12904 <- evaluateAddress v_2772;
      v_12905 <- load v_12904 16;
      setRegister (lhs.of_reg v_2773) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12905 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12905 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12905 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12905 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2781 : Mem) (v_2782 : reg (bv 256)) => do
      v_12926 <- evaluateAddress v_2781;
      v_12927 <- load v_12926 32;
      setRegister (lhs.of_reg v_2782) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12927 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
