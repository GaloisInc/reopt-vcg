def vfnmadd213ps1 : instruction :=
  definst "vfnmadd213ps" $ do
    pattern fun (v_3166 : reg (bv 128)) (v_3167 : reg (bv 128)) (v_3168 : reg (bv 128)) => do
      v_6972 <- getRegister v_3167;
      v_6974 <- getRegister v_3166;
      v_6976 <- getRegister v_3168;
      setRegister (lhs.of_reg v_3168) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6972 0 32) (extract v_6974 0 32) (extract v_6976 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6972 32 64) (extract v_6974 32 64) (extract v_6976 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6972 64 96) (extract v_6974 64 96) (extract v_6976 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6972 96 128) (extract v_6974 96 128) (extract v_6976 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3178 : reg (bv 256)) (v_3179 : reg (bv 256)) (v_3180 : reg (bv 256)) => do
      v_7000 <- getRegister v_3179;
      v_7002 <- getRegister v_3178;
      v_7004 <- getRegister v_3180;
      setRegister (lhs.of_reg v_3180) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 0 32) (extract v_7002 0 32) (extract v_7004 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 32 64) (extract v_7002 32 64) (extract v_7004 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 64 96) (extract v_7002 64 96) (extract v_7004 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 96 128) (extract v_7002 96 128) (extract v_7004 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 128 160) (extract v_7002 128 160) (extract v_7004 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 160 192) (extract v_7002 160 192) (extract v_7004 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 192 224) (extract v_7002 192 224) (extract v_7004 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7000 224 256) (extract v_7002 224 256) (extract v_7004 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3163 : Mem) (v_3161 : reg (bv 128)) (v_3162 : reg (bv 128)) => do
      v_12703 <- getRegister v_3161;
      v_12705 <- evaluateAddress v_3163;
      v_12706 <- load v_12705 16;
      v_12708 <- getRegister v_3162;
      setRegister (lhs.of_reg v_3162) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12703 0 32) (extract v_12706 0 32) (extract v_12708 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12703 32 64) (extract v_12706 32 64) (extract v_12708 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12703 64 96) (extract v_12706 64 96) (extract v_12708 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12703 96 128) (extract v_12706 96 128) (extract v_12708 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3172 : Mem) (v_3173 : reg (bv 256)) (v_3174 : reg (bv 256)) => do
      v_12727 <- getRegister v_3173;
      v_12729 <- evaluateAddress v_3172;
      v_12730 <- load v_12729 32;
      v_12732 <- getRegister v_3174;
      setRegister (lhs.of_reg v_3174) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 0 32) (extract v_12730 0 32) (extract v_12732 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 32 64) (extract v_12730 32 64) (extract v_12732 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 64 96) (extract v_12730 64 96) (extract v_12732 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 96 128) (extract v_12730 96 128) (extract v_12732 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 128 160) (extract v_12730 128 160) (extract v_12732 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 160 192) (extract v_12730 160 192) (extract v_12732 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 192 224) (extract v_12730 192 224) (extract v_12732 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12727 224 256) (extract v_12730 224 256) (extract v_12732 224 256))))))));
      pure ()
    pat_end
