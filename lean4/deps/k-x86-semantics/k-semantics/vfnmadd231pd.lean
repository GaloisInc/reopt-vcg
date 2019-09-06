def vfnmadd231pd1 : instruction :=
  definst "vfnmadd231pd" $ do
    pattern fun (v_3299 : reg (bv 128)) (v_3300 : reg (bv 128)) (v_3301 : reg (bv 128)) => do
      v_7179 <- getRegister v_3300;
      v_7181 <- getRegister v_3301;
      v_7183 <- getRegister v_3299;
      v_7194 <- eval (updateMapEntries v_2465 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3301)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7179 0 64) (extract v_7181 0 64) (extract v_7183 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7179 64 128) (extract v_7181 64 128) (extract v_7183 64 128))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3313 : reg (bv 256)) (v_3314 : reg (bv 256)) (v_3315 : reg (bv 256)) => do
      v_7200 <- getRegister v_3314;
      v_7202 <- getRegister v_3315;
      v_7204 <- getRegister v_3313;
      setRegister (lhs.of_reg v_3315) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7200 0 64) (extract v_7202 0 64) (extract v_7204 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7200 64 128) (extract v_7202 64 128) (extract v_7204 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7200 128 192) (extract v_7202 128 192) (extract v_7204 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7200 192 256) (extract v_7202 192 256) (extract v_7204 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3296 : Mem) (v_3294 : reg (bv 128)) (v_3295 : reg (bv 128)) => do
      v_12909 <- getRegister v_3294;
      v_12911 <- getRegister v_3295;
      v_12913 <- evaluateAddress v_3296;
      v_12914 <- load v_12913 16;
      v_12925 <- eval (updateMapEntries v_2465 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3295)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12909 0 64) (extract v_12911 0 64) (extract v_12914 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12909 64 128) (extract v_12911 64 128) (extract v_12914 64 128))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3305 : Mem) (v_3308 : reg (bv 256)) (v_3309 : reg (bv 256)) => do
      v_12926 <- getRegister v_3308;
      v_12928 <- getRegister v_3309;
      v_12930 <- evaluateAddress v_3305;
      v_12931 <- load v_12930 32;
      setRegister (lhs.of_reg v_3309) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12926 0 64) (extract v_12928 0 64) (extract v_12931 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12926 64 128) (extract v_12928 64 128) (extract v_12931 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12926 128 192) (extract v_12928 128 192) (extract v_12931 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12926 192 256) (extract v_12928 192 256) (extract v_12931 192 256))));
      pure ()
    pat_end
