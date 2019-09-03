def vfnmadd132ps1 : instruction :=
  definst "vfnmadd132ps" $ do
    pattern fun (v_3113 : reg (bv 128)) (v_3114 : reg (bv 128)) (v_3115 : reg (bv 128)) => do
      v_10594 <- getRegister v_3115;
      v_10596 <- getRegister v_3114;
      v_10598 <- getRegister v_3113;
      setRegister (lhs.of_reg v_3115) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10594 0 32) (extract v_10596 0 32) (extract v_10598 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10594 32 64) (extract v_10596 32 64) (extract v_10598 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10594 64 96) (extract v_10596 64 96) (extract v_10598 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10594 96 128) (extract v_10596 96 128) (extract v_10598 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3124 : reg (bv 256)) (v_3125 : reg (bv 256)) (v_3126 : reg (bv 256)) => do
      v_10622 <- getRegister v_3126;
      v_10624 <- getRegister v_3125;
      v_10626 <- getRegister v_3124;
      setRegister (lhs.of_reg v_3126) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 0 32) (extract v_10624 0 32) (extract v_10626 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 32 64) (extract v_10624 32 64) (extract v_10626 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 64 96) (extract v_10624 64 96) (extract v_10626 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 96 128) (extract v_10624 96 128) (extract v_10626 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 128 160) (extract v_10624 128 160) (extract v_10626 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 160 192) (extract v_10624 160 192) (extract v_10626 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 192 224) (extract v_10624 192 224) (extract v_10626 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10622 224 256) (extract v_10624 224 256) (extract v_10626 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3110 : Mem) (v_3108 : reg (bv 128)) (v_3109 : reg (bv 128)) => do
      v_21283 <- getRegister v_3109;
      v_21285 <- getRegister v_3108;
      v_21287 <- evaluateAddress v_3110;
      v_21288 <- load v_21287 16;
      setRegister (lhs.of_reg v_3109) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21283 0 32) (extract v_21285 0 32) (extract v_21288 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21283 32 64) (extract v_21285 32 64) (extract v_21288 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21283 64 96) (extract v_21285 64 96) (extract v_21288 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21283 96 128) (extract v_21285 96 128) (extract v_21288 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3119 : Mem) (v_3120 : reg (bv 256)) (v_3121 : reg (bv 256)) => do
      v_21307 <- getRegister v_3121;
      v_21309 <- getRegister v_3120;
      v_21311 <- evaluateAddress v_3119;
      v_21312 <- load v_21311 32;
      setRegister (lhs.of_reg v_3121) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 0 32) (extract v_21309 0 32) (extract v_21312 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 32 64) (extract v_21309 32 64) (extract v_21312 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 64 96) (extract v_21309 64 96) (extract v_21312 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 96 128) (extract v_21309 96 128) (extract v_21312 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 128 160) (extract v_21309 128 160) (extract v_21312 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 160 192) (extract v_21309 160 192) (extract v_21312 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 192 224) (extract v_21309 192 224) (extract v_21312 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21307 224 256) (extract v_21309 224 256) (extract v_21312 224 256)))))))));
      pure ()
    pat_end
