def vfnmadd231pd1 : instruction :=
  definst "vfnmadd231pd" $ do
    pattern fun (v_3275 : reg (bv 128)) (v_3276 : reg (bv 128)) (v_3277 : reg (bv 128)) => do
      v_7152 <- getRegister v_3276;
      v_7154 <- getRegister v_3277;
      v_7156 <- getRegister v_3275;
      v_7167 <- eval (updateMapEntries v_2422 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3277)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7152 0 64) (extract v_7154 0 64) (extract v_7156 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7152 64 128) (extract v_7154 64 128) (extract v_7156 64 128))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3285 : reg (bv 256)) (v_3286 : reg (bv 256)) (v_3287 : reg (bv 256)) => do
      v_7173 <- getRegister v_3286;
      v_7175 <- getRegister v_3287;
      v_7177 <- getRegister v_3285;
      setRegister (lhs.of_reg v_3287) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7173 0 64) (extract v_7175 0 64) (extract v_7177 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7173 64 128) (extract v_7175 64 128) (extract v_7177 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7173 128 192) (extract v_7175 128 192) (extract v_7177 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_7173 192 256) (extract v_7175 192 256) (extract v_7177 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3269 : Mem) (v_3270 : reg (bv 128)) (v_3271 : reg (bv 128)) => do
      v_12882 <- getRegister v_3270;
      v_12884 <- getRegister v_3271;
      v_12886 <- evaluateAddress v_3269;
      v_12887 <- load v_12886 16;
      v_12898 <- eval (updateMapEntries v_2422 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3271)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (expression.bv_nat 64 0) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12882 0 64) (extract v_12884 0 64) (extract v_12887 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12882 64 128) (extract v_12884 64 128) (extract v_12887 64 128))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3280 : Mem) (v_3281 : reg (bv 256)) (v_3282 : reg (bv 256)) => do
      v_12899 <- getRegister v_3281;
      v_12901 <- getRegister v_3282;
      v_12903 <- evaluateAddress v_3280;
      v_12904 <- load v_12903 32;
      setRegister (lhs.of_reg v_3282) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12899 0 64) (extract v_12901 0 64) (extract v_12904 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12899 64 128) (extract v_12901 64 128) (extract v_12904 64 128))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12899 128 192) (extract v_12901 128 192) (extract v_12904 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12899 192 256) (extract v_12901 192 256) (extract v_12904 192 256))));
      pure ()
    pat_end
