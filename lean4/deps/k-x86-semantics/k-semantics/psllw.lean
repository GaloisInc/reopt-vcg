def psllw1 : instruction :=
  definst "psllw" $ do
    pattern fun (v_2989 : imm int) (v_2988 : reg (bv 128)) => do
      v_7852 <- eval (handleImmediateWithSignExtend v_2989 8 8);
      v_7855 <- getRegister v_2988;
      v_7856 <- eval (extract v_7855 0 16);
      v_7858 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_7852));
      v_7862 <- eval (extract v_7855 16 32);
      v_7866 <- eval (extract v_7855 32 48);
      v_7870 <- eval (extract v_7855 48 64);
      v_7874 <- eval (extract v_7855 64 80);
      v_7878 <- eval (extract v_7855 80 96);
      v_7882 <- eval (extract v_7855 96 112);
      v_7886 <- eval (extract v_7855 112 128);
      setRegister (lhs.of_reg v_2988) (mux (ugt (concat (expression.bv_nat 56 0) v_7852) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl v_7856 v_7858) 0 (bitwidthMInt v_7856)) (concat (extract (shl v_7862 v_7858) 0 (bitwidthMInt v_7862)) (concat (extract (shl v_7866 v_7858) 0 (bitwidthMInt v_7866)) (concat (extract (shl v_7870 v_7858) 0 (bitwidthMInt v_7870)) (concat (extract (shl v_7874 v_7858) 0 (bitwidthMInt v_7874)) (concat (extract (shl v_7878 v_7858) 0 (bitwidthMInt v_7878)) (concat (extract (shl v_7882 v_7858) 0 (bitwidthMInt v_7882)) (extract (shl v_7886 v_7858) 0 (bitwidthMInt v_7886))))))))));
      pure ()
    pat_end;
    pattern fun (v_2997 : reg (bv 128)) (v_2998 : reg (bv 128)) => do
      v_7903 <- getRegister v_2997;
      v_7906 <- getRegister v_2998;
      v_7907 <- eval (extract v_7906 0 16);
      v_7909 <- eval (uvalueMInt (extract v_7903 112 128));
      v_7913 <- eval (extract v_7906 16 32);
      v_7917 <- eval (extract v_7906 32 48);
      v_7921 <- eval (extract v_7906 48 64);
      v_7925 <- eval (extract v_7906 64 80);
      v_7929 <- eval (extract v_7906 80 96);
      v_7933 <- eval (extract v_7906 96 112);
      v_7937 <- eval (extract v_7906 112 128);
      setRegister (lhs.of_reg v_2998) (mux (ugt (extract v_7903 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl v_7907 v_7909) 0 (bitwidthMInt v_7907)) (concat (extract (shl v_7913 v_7909) 0 (bitwidthMInt v_7913)) (concat (extract (shl v_7917 v_7909) 0 (bitwidthMInt v_7917)) (concat (extract (shl v_7921 v_7909) 0 (bitwidthMInt v_7921)) (concat (extract (shl v_7925 v_7909) 0 (bitwidthMInt v_7925)) (concat (extract (shl v_7929 v_7909) 0 (bitwidthMInt v_7929)) (concat (extract (shl v_7933 v_7909) 0 (bitwidthMInt v_7933)) (extract (shl v_7937 v_7909) 0 (bitwidthMInt v_7937))))))))));
      pure ()
    pat_end;
    pattern fun (v_2992 : Mem) (v_2993 : reg (bv 128)) => do
      v_14997 <- evaluateAddress v_2992;
      v_14998 <- load v_14997 16;
      v_15001 <- getRegister v_2993;
      v_15002 <- eval (extract v_15001 0 16);
      v_15004 <- eval (uvalueMInt (extract v_14998 112 128));
      v_15008 <- eval (extract v_15001 16 32);
      v_15012 <- eval (extract v_15001 32 48);
      v_15016 <- eval (extract v_15001 48 64);
      v_15020 <- eval (extract v_15001 64 80);
      v_15024 <- eval (extract v_15001 80 96);
      v_15028 <- eval (extract v_15001 96 112);
      v_15032 <- eval (extract v_15001 112 128);
      setRegister (lhs.of_reg v_2993) (mux (ugt (extract v_14998 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl v_15002 v_15004) 0 (bitwidthMInt v_15002)) (concat (extract (shl v_15008 v_15004) 0 (bitwidthMInt v_15008)) (concat (extract (shl v_15012 v_15004) 0 (bitwidthMInt v_15012)) (concat (extract (shl v_15016 v_15004) 0 (bitwidthMInt v_15016)) (concat (extract (shl v_15020 v_15004) 0 (bitwidthMInt v_15020)) (concat (extract (shl v_15024 v_15004) 0 (bitwidthMInt v_15024)) (concat (extract (shl v_15028 v_15004) 0 (bitwidthMInt v_15028)) (extract (shl v_15032 v_15004) 0 (bitwidthMInt v_15032))))))))));
      pure ()
    pat_end
