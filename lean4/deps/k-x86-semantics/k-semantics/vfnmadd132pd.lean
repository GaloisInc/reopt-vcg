def vfnmadd132pd1 : instruction :=
  definst "vfnmadd132pd" $ do
    pattern fun (v_3078 : reg (bv 128)) (v_3079 : reg (bv 128)) (v_3080 : reg (bv 128)) => do
      v_6774 <- getRegister v_3080;
      v_6776 <- getRegister v_3079;
      v_6778 <- getRegister v_3078;
      setRegister (lhs.of_reg v_3080) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6774 0 64) (extract v_6776 0 64) (extract v_6778 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6774 64 128) (extract v_6776 64 128) (extract v_6778 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3090 : reg (bv 256)) (v_3091 : reg (bv 256)) (v_3092 : reg (bv 256)) => do
      v_6792 <- getRegister v_3092;
      v_6794 <- getRegister v_3091;
      v_6796 <- getRegister v_3090;
      setRegister (lhs.of_reg v_3092) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6792 0 64) (extract v_6794 0 64) (extract v_6796 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6792 64 128) (extract v_6794 64 128) (extract v_6796 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6792 128 192) (extract v_6794 128 192) (extract v_6796 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6792 192 256) (extract v_6794 192 256) (extract v_6796 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3075 : Mem) (v_3073 : reg (bv 128)) (v_3074 : reg (bv 128)) => do
      v_12539 <- getRegister v_3074;
      v_12541 <- getRegister v_3073;
      v_12543 <- evaluateAddress v_3075;
      v_12544 <- load v_12543 16;
      setRegister (lhs.of_reg v_3074) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12539 0 64) (extract v_12541 0 64) (extract v_12544 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12539 64 128) (extract v_12541 64 128) (extract v_12544 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3084 : Mem) (v_3085 : reg (bv 256)) (v_3086 : reg (bv 256)) => do
      v_12553 <- getRegister v_3086;
      v_12555 <- getRegister v_3085;
      v_12557 <- evaluateAddress v_3084;
      v_12558 <- load v_12557 32;
      setRegister (lhs.of_reg v_3086) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12553 0 64) (extract v_12555 0 64) (extract v_12558 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12553 64 128) (extract v_12555 64 128) (extract v_12558 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12553 128 192) (extract v_12555 128 192) (extract v_12558 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12553 192 256) (extract v_12555 192 256) (extract v_12558 192 256)))));
      pure ()
    pat_end
