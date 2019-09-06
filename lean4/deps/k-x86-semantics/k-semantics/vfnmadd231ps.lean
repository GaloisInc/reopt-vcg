def vfnmadd231ps1 : instruction :=
  definst "vfnmadd231ps" $ do
    pattern fun (v_3321 : reg (bv 128)) (v_3322 : reg (bv 128)) (v_3323 : reg (bv 128)) => do
      v_7228 <- getRegister v_3322;
      v_7230 <- getRegister v_3323;
      v_7232 <- getRegister v_3321;
      setRegister (lhs.of_reg v_3323) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7228 0 32) (extract v_7230 0 32) (extract v_7232 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7228 32 64) (extract v_7230 32 64) (extract v_7232 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7228 64 96) (extract v_7230 64 96) (extract v_7232 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7228 96 128) (extract v_7230 96 128) (extract v_7232 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3335 : reg (bv 256)) (v_3336 : reg (bv 256)) (v_3337 : reg (bv 256)) => do
      v_7256 <- getRegister v_3336;
      v_7258 <- getRegister v_3337;
      v_7260 <- getRegister v_3335;
      setRegister (lhs.of_reg v_3337) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 0 32) (extract v_7258 0 32) (extract v_7260 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 32 64) (extract v_7258 32 64) (extract v_7260 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 64 96) (extract v_7258 64 96) (extract v_7260 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 96 128) (extract v_7258 96 128) (extract v_7260 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 128 160) (extract v_7258 128 160) (extract v_7260 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 160 192) (extract v_7258 160 192) (extract v_7260 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 192 224) (extract v_7258 192 224) (extract v_7260 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7256 224 256) (extract v_7258 224 256) (extract v_7260 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_3318 : Mem) (v_3316 : reg (bv 128)) (v_3317 : reg (bv 128)) => do
      v_12950 <- getRegister v_3316;
      v_12952 <- getRegister v_3317;
      v_12954 <- evaluateAddress v_3318;
      v_12955 <- load v_12954 16;
      setRegister (lhs.of_reg v_3317) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12950 0 32) (extract v_12952 0 32) (extract v_12955 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12950 32 64) (extract v_12952 32 64) (extract v_12955 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12950 64 96) (extract v_12952 64 96) (extract v_12955 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12950 96 128) (extract v_12952 96 128) (extract v_12955 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3327 : Mem) (v_3330 : reg (bv 256)) (v_3331 : reg (bv 256)) => do
      v_12974 <- getRegister v_3330;
      v_12976 <- getRegister v_3331;
      v_12978 <- evaluateAddress v_3327;
      v_12979 <- load v_12978 32;
      setRegister (lhs.of_reg v_3331) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 0 32) (extract v_12976 0 32) (extract v_12979 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 32 64) (extract v_12976 32 64) (extract v_12979 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 64 96) (extract v_12976 64 96) (extract v_12979 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 96 128) (extract v_12976 96 128) (extract v_12979 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 128 160) (extract v_12976 128 160) (extract v_12979 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 160 192) (extract v_12976 160 192) (extract v_12979 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 192 224) (extract v_12976 192 224) (extract v_12979 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12974 224 256) (extract v_12976 224 256) (extract v_12979 224 256))))));
      pure ()
    pat_end
