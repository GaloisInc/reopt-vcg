def vaddps1 : instruction :=
  definst "vaddps" $ do
    pattern fun (v_2656 : reg (bv 128)) (v_2657 : reg (bv 128)) (v_2658 : reg (bv 128)) => do
      v_4841 <- getRegister v_2657;
      v_4844 <- getRegister v_2656;
      setRegister (lhs.of_reg v_2658) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4841 0 32) 24 8) (MInt2Float (extract v_4844 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4841 32 64) 24 8) (MInt2Float (extract v_4844 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4841 64 96) 24 8) (MInt2Float (extract v_4844 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4841 96 128) 24 8) (MInt2Float (extract v_4844 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2666 : reg (bv 256)) (v_2667 : reg (bv 256)) (v_2668 : reg (bv 256)) => do
      v_4876 <- getRegister v_2667;
      v_4879 <- getRegister v_2666;
      setRegister (lhs.of_reg v_2668) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 0 32) 24 8) (MInt2Float (extract v_4879 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 32 64) 24 8) (MInt2Float (extract v_4879 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 64 96) 24 8) (MInt2Float (extract v_4879 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 96 128) 24 8) (MInt2Float (extract v_4879 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 128 160) 24 8) (MInt2Float (extract v_4879 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 160 192) 24 8) (MInt2Float (extract v_4879 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 192 224) 24 8) (MInt2Float (extract v_4879 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4876 224 256) 24 8) (MInt2Float (extract v_4879 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2650 : Mem) (v_2651 : reg (bv 128)) (v_2652 : reg (bv 128)) => do
      v_9142 <- getRegister v_2651;
      v_9145 <- evaluateAddress v_2650;
      v_9146 <- load v_9145 16;
      setRegister (lhs.of_reg v_2652) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9142 0 32) 24 8) (MInt2Float (extract v_9146 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9142 32 64) 24 8) (MInt2Float (extract v_9146 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9142 64 96) 24 8) (MInt2Float (extract v_9146 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9142 96 128) 24 8) (MInt2Float (extract v_9146 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2661 : Mem) (v_2662 : reg (bv 256)) (v_2663 : reg (bv 256)) => do
      v_9173 <- getRegister v_2662;
      v_9176 <- evaluateAddress v_2661;
      v_9177 <- load v_9176 32;
      setRegister (lhs.of_reg v_2663) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 0 32) 24 8) (MInt2Float (extract v_9177 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 32 64) 24 8) (MInt2Float (extract v_9177 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 64 96) 24 8) (MInt2Float (extract v_9177 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 96 128) 24 8) (MInt2Float (extract v_9177 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 128 160) 24 8) (MInt2Float (extract v_9177 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 160 192) 24 8) (MInt2Float (extract v_9177 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 192 224) 24 8) (MInt2Float (extract v_9177 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9173 224 256) 24 8) (MInt2Float (extract v_9177 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
