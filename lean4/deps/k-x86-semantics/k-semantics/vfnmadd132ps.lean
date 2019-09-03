def vfnmadd132ps1 : instruction :=
  definst "vfnmadd132ps" $ do
    pattern fun (v_3100 : reg (bv 128)) (v_3101 : reg (bv 128)) (v_3102 : reg (bv 128)) => do
      v_6820 <- getRegister v_3102;
      v_6822 <- getRegister v_3101;
      v_6824 <- getRegister v_3100;
      setRegister (lhs.of_reg v_3102) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6820 0 32) (extract v_6822 0 32) (extract v_6824 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6820 32 64) (extract v_6822 32 64) (extract v_6824 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6820 64 96) (extract v_6822 64 96) (extract v_6824 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6820 96 128) (extract v_6822 96 128) (extract v_6824 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3112 : reg (bv 256)) (v_3113 : reg (bv 256)) (v_3114 : reg (bv 256)) => do
      v_6848 <- getRegister v_3114;
      v_6850 <- getRegister v_3113;
      v_6852 <- getRegister v_3112;
      setRegister (lhs.of_reg v_3114) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 0 32) (extract v_6850 0 32) (extract v_6852 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 32 64) (extract v_6850 32 64) (extract v_6852 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 64 96) (extract v_6850 64 96) (extract v_6852 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 96 128) (extract v_6850 96 128) (extract v_6852 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 128 160) (extract v_6850 128 160) (extract v_6852 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 160 192) (extract v_6850 160 192) (extract v_6852 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 192 224) (extract v_6850 192 224) (extract v_6852 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6848 224 256) (extract v_6850 224 256) (extract v_6852 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3097 : Mem) (v_3095 : reg (bv 128)) (v_3096 : reg (bv 128)) => do
      v_12577 <- getRegister v_3096;
      v_12579 <- getRegister v_3095;
      v_12581 <- evaluateAddress v_3097;
      v_12582 <- load v_12581 16;
      setRegister (lhs.of_reg v_3096) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12577 0 32) (extract v_12579 0 32) (extract v_12582 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12577 32 64) (extract v_12579 32 64) (extract v_12582 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12577 64 96) (extract v_12579 64 96) (extract v_12582 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12577 96 128) (extract v_12579 96 128) (extract v_12582 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3106 : Mem) (v_3107 : reg (bv 256)) (v_3108 : reg (bv 256)) => do
      v_12601 <- getRegister v_3108;
      v_12603 <- getRegister v_3107;
      v_12605 <- evaluateAddress v_3106;
      v_12606 <- load v_12605 32;
      setRegister (lhs.of_reg v_3108) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 0 32) (extract v_12603 0 32) (extract v_12606 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 32 64) (extract v_12603 32 64) (extract v_12606 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 64 96) (extract v_12603 64 96) (extract v_12606 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 96 128) (extract v_12603 96 128) (extract v_12606 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 128 160) (extract v_12603 128 160) (extract v_12606 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 160 192) (extract v_12603 160 192) (extract v_12606 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 192 224) (extract v_12603 192 224) (extract v_12606 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12601 224 256) (extract v_12603 224 256) (extract v_12606 224 256)))))))));
      pure ()
    pat_end
