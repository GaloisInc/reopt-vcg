def vfnmadd213ps1 : instruction :=
  definst "vfnmadd213ps" $ do
    pattern fun (v_3231 : reg (bv 128)) (v_3232 : reg (bv 128)) (v_3233 : reg (bv 128)) => do
      v_7041 <- getRegister v_3232;
      v_7043 <- getRegister v_3231;
      v_7045 <- getRegister v_3233;
      v_7066 <- eval (updateMapEntries v_2422 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3233)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32)))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7041 0 32) (extract v_7043 0 32) (extract v_7045 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7041 32 64) (extract v_7043 32 64) (extract v_7045 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7041 64 96) (extract v_7043 64 96) (extract v_7045 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7041 96 128) (extract v_7043 96 128) (extract v_7045 96 128))))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3241 : reg (bv 256)) (v_3242 : reg (bv 256)) (v_3243 : reg (bv 256)) => do
      v_7072 <- getRegister v_3242;
      v_7074 <- getRegister v_3241;
      v_7076 <- getRegister v_3243;
      setRegister (lhs.of_reg v_3243) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 0 32) (extract v_7074 0 32) (extract v_7076 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 32 64) (extract v_7074 32 64) (extract v_7076 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 64 96) (extract v_7074 64 96) (extract v_7076 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 96 128) (extract v_7074 96 128) (extract v_7076 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 128 160) (extract v_7074 128 160) (extract v_7076 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 160 192) (extract v_7074 160 192) (extract v_7076 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 192 224) (extract v_7074 192 224) (extract v_7076 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7072 224 256) (extract v_7074 224 256) (extract v_7076 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3225 : Mem) (v_3226 : reg (bv 128)) (v_3227 : reg (bv 128)) => do
      v_12789 <- getRegister v_3226;
      v_12791 <- evaluateAddress v_3225;
      v_12792 <- load v_12791 16;
      v_12794 <- getRegister v_3227;
      v_12815 <- eval (updateMapEntries v_2422 (_,__X86-LEAN (mapEntry (convToRegKeysHelper (convSubRegsToRegs v_3227)) (concat (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32) (Float2MInt (_+Float__FLOAT (--Float__FLOAT (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) (MInt2Float (expression.bv_nat 32 0) 24 8))) (MInt2Float (expression.bv_nat 32 0) 24 8)) 32)))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12789 0 32) (extract v_12792 0 32) (extract v_12794 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12789 32 64) (extract v_12792 32 64) (extract v_12794 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12789 64 96) (extract v_12792 64 96) (extract v_12794 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12789 96 128) (extract v_12792 96 128) (extract v_12794 96 128))))))) .List{"_,__X86-LEAN"}));
      pure ()
    pat_end;
    pattern fun (v_3236 : Mem) (v_3237 : reg (bv 256)) (v_3238 : reg (bv 256)) => do
      v_12816 <- getRegister v_3237;
      v_12818 <- evaluateAddress v_3236;
      v_12819 <- load v_12818 32;
      v_12821 <- getRegister v_3238;
      setRegister (lhs.of_reg v_3238) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 0 32) (extract v_12819 0 32) (extract v_12821 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 32 64) (extract v_12819 32 64) (extract v_12821 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 64 96) (extract v_12819 64 96) (extract v_12821 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 96 128) (extract v_12819 96 128) (extract v_12821 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 128 160) (extract v_12819 128 160) (extract v_12821 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 160 192) (extract v_12819 160 192) (extract v_12821 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 192 224) (extract v_12819 192 224) (extract v_12821 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12816 224 256) (extract v_12819 224 256) (extract v_12821 224 256))))))));
      pure ()
    pat_end
