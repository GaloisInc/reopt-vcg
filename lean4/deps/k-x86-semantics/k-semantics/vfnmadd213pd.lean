def vfnmadd213pd1 : instruction :=
  definst "vfnmadd213pd" $ do
    pattern fun (v_3157 : reg (bv 128)) (v_3158 : reg (bv 128)) (v_3159 : reg (bv 128)) => do
      v_10700 <- getRegister v_3158;
      v_10702 <- getRegister v_3157;
      v_10704 <- getRegister v_3159;
      setRegister (lhs.of_reg v_3159) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10700 0 64) (extract v_10702 0 64) (extract v_10704 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10700 64 128) (extract v_10702 64 128) (extract v_10704 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3168 : reg (bv 256)) (v_3169 : reg (bv 256)) (v_3170 : reg (bv 256)) => do
      v_10718 <- getRegister v_3169;
      v_10720 <- getRegister v_3168;
      v_10722 <- getRegister v_3170;
      setRegister (lhs.of_reg v_3170) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10718 0 64) (extract v_10720 0 64) (extract v_10722 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10718 64 128) (extract v_10720 64 128) (extract v_10722 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10718 128 192) (extract v_10720 128 192) (extract v_10722 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_10718 192 256) (extract v_10720 192 256) (extract v_10722 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3154 : Mem) (v_3152 : reg (bv 128)) (v_3153 : reg (bv 128)) => do
      v_21371 <- getRegister v_3152;
      v_21373 <- evaluateAddress v_3154;
      v_21374 <- load v_21373 16;
      v_21376 <- getRegister v_3153;
      setRegister (lhs.of_reg v_3153) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21371 0 64) (extract v_21374 0 64) (extract v_21376 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21371 64 128) (extract v_21374 64 128) (extract v_21376 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3163 : Mem) (v_3164 : reg (bv 256)) (v_3165 : reg (bv 256)) => do
      v_21385 <- getRegister v_3164;
      v_21387 <- evaluateAddress v_3163;
      v_21388 <- load v_21387 32;
      v_21390 <- getRegister v_3165;
      setRegister (lhs.of_reg v_3165) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21385 0 64) (extract v_21388 0 64) (extract v_21390 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21385 64 128) (extract v_21388 64 128) (extract v_21390 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21385 128 192) (extract v_21388 128 192) (extract v_21390 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_21385 192 256) (extract v_21388 192 256) (extract v_21390 192 256)))));
      pure ()
    pat_end
