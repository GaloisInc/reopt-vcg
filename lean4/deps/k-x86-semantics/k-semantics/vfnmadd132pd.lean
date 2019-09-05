def vfnmadd132pd1 : instruction :=
  definst "vfnmadd132pd" $ do
    pattern fun (v_3143 : reg (bv 128)) (v_3144 : reg (bv 128)) (v_3145 : reg (bv 128)) => do
      v_6841 <- getRegister v_3145;
      v_6843 <- getRegister v_3144;
      v_6845 <- getRegister v_3143;
      setRegister (lhs.of_reg v_3145) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6841 0 64) (extract v_6843 0 64) (extract v_6845 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6841 64 128) (extract v_6843 64 128) (extract v_6845 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3153 : reg (bv 256)) (v_3154 : reg (bv 256)) (v_3155 : reg (bv 256)) => do
      v_6859 <- getRegister v_3155;
      v_6861 <- getRegister v_3154;
      v_6863 <- getRegister v_3153;
      setRegister (lhs.of_reg v_3155) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6859 0 64) (extract v_6861 0 64) (extract v_6863 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6859 64 128) (extract v_6861 64 128) (extract v_6863 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6859 128 192) (extract v_6861 128 192) (extract v_6863 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6859 192 256) (extract v_6861 192 256) (extract v_6863 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3137 : Mem) (v_3138 : reg (bv 128)) (v_3139 : reg (bv 128)) => do
      v_12623 <- getRegister v_3139;
      v_12625 <- getRegister v_3138;
      v_12627 <- evaluateAddress v_3137;
      v_12628 <- load v_12627 16;
      setRegister (lhs.of_reg v_3139) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12623 0 64) (extract v_12625 0 64) (extract v_12628 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12623 64 128) (extract v_12625 64 128) (extract v_12628 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3148 : Mem) (v_3149 : reg (bv 256)) (v_3150 : reg (bv 256)) => do
      v_12637 <- getRegister v_3150;
      v_12639 <- getRegister v_3149;
      v_12641 <- evaluateAddress v_3148;
      v_12642 <- load v_12641 32;
      setRegister (lhs.of_reg v_3150) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12637 0 64) (extract v_12639 0 64) (extract v_12642 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12637 64 128) (extract v_12639 64 128) (extract v_12642 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12637 128 192) (extract v_12639 128 192) (extract v_12642 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12637 192 256) (extract v_12639 192 256) (extract v_12642 192 256)))));
      pure ()
    pat_end
