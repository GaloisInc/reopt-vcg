def vfnmadd231ps1 : instruction :=
  definst "vfnmadd231ps" $ do
    pattern fun (v_3297 : reg (bv 128)) (v_3298 : reg (bv 128)) (v_3299 : reg (bv 128)) => do
      v_7201 <- getRegister v_3298;
      v_7203 <- getRegister v_3299;
      v_7205 <- getRegister v_3297;
      setRegister (lhs.of_reg v_3299) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7201 0 32) (extract v_7203 0 32) (extract v_7205 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7201 32 64) (extract v_7203 32 64) (extract v_7205 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7201 64 96) (extract v_7203 64 96) (extract v_7205 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7201 96 128) (extract v_7203 96 128) (extract v_7205 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3307 : reg (bv 256)) (v_3308 : reg (bv 256)) (v_3309 : reg (bv 256)) => do
      v_7229 <- getRegister v_3308;
      v_7231 <- getRegister v_3309;
      v_7233 <- getRegister v_3307;
      setRegister (lhs.of_reg v_3309) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 0 32) (extract v_7231 0 32) (extract v_7233 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 32 64) (extract v_7231 32 64) (extract v_7233 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 64 96) (extract v_7231 64 96) (extract v_7233 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 96 128) (extract v_7231 96 128) (extract v_7233 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 128 160) (extract v_7231 128 160) (extract v_7233 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 160 192) (extract v_7231 160 192) (extract v_7233 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 192 224) (extract v_7231 192 224) (extract v_7233 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7229 224 256) (extract v_7231 224 256) (extract v_7233 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_3291 : Mem) (v_3292 : reg (bv 128)) (v_3293 : reg (bv 128)) => do
      v_12923 <- getRegister v_3292;
      v_12925 <- getRegister v_3293;
      v_12927 <- evaluateAddress v_3291;
      v_12928 <- load v_12927 16;
      setRegister (lhs.of_reg v_3293) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12923 0 32) (extract v_12925 0 32) (extract v_12928 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12923 32 64) (extract v_12925 32 64) (extract v_12928 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12923 64 96) (extract v_12925 64 96) (extract v_12928 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12923 96 128) (extract v_12925 96 128) (extract v_12928 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3302 : Mem) (v_3303 : reg (bv 256)) (v_3304 : reg (bv 256)) => do
      v_12947 <- getRegister v_3303;
      v_12949 <- getRegister v_3304;
      v_12951 <- evaluateAddress v_3302;
      v_12952 <- load v_12951 32;
      setRegister (lhs.of_reg v_3304) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 0 32) (extract v_12949 0 32) (extract v_12952 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 32 64) (extract v_12949 32 64) (extract v_12952 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 64 96) (extract v_12949 64 96) (extract v_12952 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 96 128) (extract v_12949 96 128) (extract v_12952 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 128 160) (extract v_12949 128 160) (extract v_12952 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 160 192) (extract v_12949 160 192) (extract v_12952 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 192 224) (extract v_12949 192 224) (extract v_12952 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12947 224 256) (extract v_12949 224 256) (extract v_12952 224 256))))));
      pure ()
    pat_end
