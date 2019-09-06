def vfnmadd213ps1 : instruction :=
  definst "vfnmadd213ps" $ do
    pattern fun (v_3255 : reg (bv 128)) (v_3256 : reg (bv 128)) (v_3257 : reg (bv 128)) => do
      v_7068 <- getRegister v_3256;
      v_7070 <- getRegister v_3255;
      v_7072 <- getRegister v_3257;
      v_7093 <- eval (updateMapEntries v_2465 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3257)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32)))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7068 0 32) (extract v_7070 0 32) (extract v_7072 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7068 32 64) (extract v_7070 32 64) (extract v_7072 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7068 64 96) (extract v_7070 64 96) (extract v_7072 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7068 96 128) (extract v_7070 96 128) (extract v_7072 96 128))))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3269 : reg (bv 256)) (v_3270 : reg (bv 256)) (v_3271 : reg (bv 256)) => do
      v_7099 <- getRegister v_3270;
      v_7101 <- getRegister v_3269;
      v_7103 <- getRegister v_3271;
      setRegister (lhs.of_reg v_3271) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 0 32) (extract v_7101 0 32) (extract v_7103 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 32 64) (extract v_7101 32 64) (extract v_7103 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 64 96) (extract v_7101 64 96) (extract v_7103 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 96 128) (extract v_7101 96 128) (extract v_7103 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 128 160) (extract v_7101 128 160) (extract v_7103 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 160 192) (extract v_7101 160 192) (extract v_7103 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 192 224) (extract v_7101 192 224) (extract v_7103 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7099 224 256) (extract v_7101 224 256) (extract v_7103 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3252 : Mem) (v_3250 : reg (bv 128)) (v_3251 : reg (bv 128)) => do
      v_12816 <- getRegister v_3250;
      v_12818 <- evaluateAddress v_3252;
      v_12819 <- load v_12818 16;
      v_12821 <- getRegister v_3251;
      v_12842 <- eval (updateMapEntries v_2465 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3251)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32)))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 0 32) (extract v_12819 0 32) (extract v_12821 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 32 64) (extract v_12819 32 64) (extract v_12821 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 64 96) (extract v_12819 64 96) (extract v_12821 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 96 128) (extract v_12819 96 128) (extract v_12821 96 128))))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3261 : Mem) (v_3264 : reg (bv 256)) (v_3265 : reg (bv 256)) => do
      v_12843 <- getRegister v_3264;
      v_12845 <- evaluateAddress v_3261;
      v_12846 <- load v_12845 32;
      v_12848 <- getRegister v_3265;
      setRegister (lhs.of_reg v_3265) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 0 32) (extract v_12846 0 32) (extract v_12848 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 32 64) (extract v_12846 32 64) (extract v_12848 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 64 96) (extract v_12846 64 96) (extract v_12848 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 96 128) (extract v_12846 96 128) (extract v_12848 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 128 160) (extract v_12846 128 160) (extract v_12848 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 160 192) (extract v_12846 160 192) (extract v_12848 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 192 224) (extract v_12846 192 224) (extract v_12848 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12843 224 256) (extract v_12846 224 256) (extract v_12848 224 256))))))));
      pure ()
    pat_end
