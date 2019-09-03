def vfnmadd213pd1 : instruction :=
  definst "vfnmadd213pd" $ do
    pattern fun (v_3144 : reg (bv 128)) (v_3145 : reg (bv 128)) (v_3146 : reg (bv 128)) => do
      v_6926 <- getRegister v_3145;
      v_6928 <- getRegister v_3144;
      v_6930 <- getRegister v_3146;
      setRegister (lhs.of_reg v_3146) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6926 0 64) (extract v_6928 0 64) (extract v_6930 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6926 64 128) (extract v_6928 64 128) (extract v_6930 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3156 : reg (bv 256)) (v_3157 : reg (bv 256)) (v_3158 : reg (bv 256)) => do
      v_6944 <- getRegister v_3157;
      v_6946 <- getRegister v_3156;
      v_6948 <- getRegister v_3158;
      setRegister (lhs.of_reg v_3158) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6944 0 64) (extract v_6946 0 64) (extract v_6948 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6944 64 128) (extract v_6946 64 128) (extract v_6948 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6944 128 192) (extract v_6946 128 192) (extract v_6948 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6944 192 256) (extract v_6946 192 256) (extract v_6948 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3141 : Mem) (v_3139 : reg (bv 128)) (v_3140 : reg (bv 128)) => do
      v_12665 <- getRegister v_3139;
      v_12667 <- evaluateAddress v_3141;
      v_12668 <- load v_12667 16;
      v_12670 <- getRegister v_3140;
      setRegister (lhs.of_reg v_3140) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12665 0 64) (extract v_12668 0 64) (extract v_12670 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12665 64 128) (extract v_12668 64 128) (extract v_12670 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3150 : Mem) (v_3151 : reg (bv 256)) (v_3152 : reg (bv 256)) => do
      v_12679 <- getRegister v_3151;
      v_12681 <- evaluateAddress v_3150;
      v_12682 <- load v_12681 32;
      v_12684 <- getRegister v_3152;
      setRegister (lhs.of_reg v_3152) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12679 0 64) (extract v_12682 0 64) (extract v_12684 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12679 64 128) (extract v_12682 64 128) (extract v_12684 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12679 128 192) (extract v_12682 128 192) (extract v_12684 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12679 192 256) (extract v_12682 192 256) (extract v_12684 192 256)))));
      pure ()
    pat_end
