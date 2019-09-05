def vshufpd1 : instruction :=
  definst "vshufpd" $ do
    pattern fun (v_2974 : imm int) (v_2971 : reg (bv 128)) (v_2972 : reg (bv 128)) (v_2973 : reg (bv 128)) => do
      v_6851 <- eval (handleImmediateWithSignExtend v_2974 8 8);
      v_6853 <- getRegister v_2971;
      v_6858 <- getRegister v_2972;
      setRegister (lhs.of_reg v_2973) (concat (mux (isBitSet v_6851 6) (extract v_6853 0 64) (extract v_6853 64 128)) (mux (isBitSet v_6851 7) (extract v_6858 0 64) (extract v_6858 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2987 : imm int) (v_2984 : reg (bv 256)) (v_2985 : reg (bv 256)) (v_2986 : reg (bv 256)) => do
      v_6870 <- eval (handleImmediateWithSignExtend v_2987 8 8);
      v_6872 <- getRegister v_2984;
      v_6877 <- getRegister v_2985;
      setRegister (lhs.of_reg v_2986) (concat (mux (isBitSet v_6870 4) (extract v_6872 0 64) (extract v_6872 64 128)) (concat (mux (isBitSet v_6870 5) (extract v_6877 0 64) (extract v_6877 64 128)) (concat (mux (isBitSet v_6870 6) (extract v_6872 128 192) (extract v_6872 192 256)) (mux (isBitSet v_6870 7) (extract v_6877 128 192) (extract v_6877 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2967 : imm int) (v_2964 : Mem) (v_2965 : reg (bv 128)) (v_2966 : reg (bv 128)) => do
      v_12818 <- eval (handleImmediateWithSignExtend v_2967 8 8);
      v_12820 <- evaluateAddress v_2964;
      v_12821 <- load v_12820 16;
      v_12826 <- getRegister v_2965;
      setRegister (lhs.of_reg v_2966) (concat (mux (isBitSet v_12818 6) (extract v_12821 0 64) (extract v_12821 64 128)) (mux (isBitSet v_12818 7) (extract v_12826 0 64) (extract v_12826 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2980 : imm int) (v_2977 : Mem) (v_2978 : reg (bv 256)) (v_2979 : reg (bv 256)) => do
      v_12832 <- eval (handleImmediateWithSignExtend v_2980 8 8);
      v_12834 <- evaluateAddress v_2977;
      v_12835 <- load v_12834 32;
      v_12840 <- getRegister v_2978;
      setRegister (lhs.of_reg v_2979) (concat (mux (isBitSet v_12832 4) (extract v_12835 0 64) (extract v_12835 64 128)) (concat (mux (isBitSet v_12832 5) (extract v_12840 0 64) (extract v_12840 64 128)) (concat (mux (isBitSet v_12832 6) (extract v_12835 128 192) (extract v_12835 192 256)) (mux (isBitSet v_12832 7) (extract v_12840 128 192) (extract v_12840 192 256)))));
      pure ()
    pat_end
