def vfnmadd213pd1 : instruction :=
  definst "vfnmadd213pd" $ do
    pattern fun (v_3209 : reg (bv 128)) (v_3210 : reg (bv 128)) (v_3211 : reg (bv 128)) => do
      v_6993 <- getRegister v_3210;
      v_6995 <- getRegister v_3209;
      v_6997 <- getRegister v_3211;
      setRegister (lhs.of_reg v_3211) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6993 0 64) (extract v_6995 0 64) (extract v_6997 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6993 64 128) (extract v_6995 64 128) (extract v_6997 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3219 : reg (bv 256)) (v_3220 : reg (bv 256)) (v_3221 : reg (bv 256)) => do
      v_7011 <- getRegister v_3220;
      v_7013 <- getRegister v_3219;
      v_7015 <- getRegister v_3221;
      setRegister (lhs.of_reg v_3221) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7011 0 64) (extract v_7013 0 64) (extract v_7015 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7011 64 128) (extract v_7013 64 128) (extract v_7015 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7011 128 192) (extract v_7013 128 192) (extract v_7015 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7011 192 256) (extract v_7013 192 256) (extract v_7015 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3203 : Mem) (v_3204 : reg (bv 128)) (v_3205 : reg (bv 128)) => do
      v_12749 <- getRegister v_3204;
      v_12751 <- evaluateAddress v_3203;
      v_12752 <- load v_12751 16;
      v_12754 <- getRegister v_3205;
      setRegister (lhs.of_reg v_3205) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12749 0 64) (extract v_12752 0 64) (extract v_12754 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12749 64 128) (extract v_12752 64 128) (extract v_12754 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3214 : Mem) (v_3215 : reg (bv 256)) (v_3216 : reg (bv 256)) => do
      v_12763 <- getRegister v_3215;
      v_12765 <- evaluateAddress v_3214;
      v_12766 <- load v_12765 32;
      v_12768 <- getRegister v_3216;
      setRegister (lhs.of_reg v_3216) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12763 0 64) (extract v_12766 0 64) (extract v_12768 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12763 64 128) (extract v_12766 64 128) (extract v_12768 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12763 128 192) (extract v_12766 128 192) (extract v_12768 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12763 192 256) (extract v_12766 192 256) (extract v_12768 192 256)))));
      pure ()
    pat_end
