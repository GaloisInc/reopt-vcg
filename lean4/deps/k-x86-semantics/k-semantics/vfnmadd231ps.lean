def vfnmadd231ps1 : instruction :=
  definst "vfnmadd231ps" $ do
    pattern fun (v_3232 : reg (bv 128)) (v_3233 : reg (bv 128)) (v_3234 : reg (bv 128)) => do
      v_7124 <- getRegister v_3233;
      v_7126 <- getRegister v_3234;
      v_7128 <- getRegister v_3232;
      setRegister (lhs.of_reg v_3234) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7124 0 32) (extract v_7126 0 32) (extract v_7128 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7124 32 64) (extract v_7126 32 64) (extract v_7128 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7124 64 96) (extract v_7126 64 96) (extract v_7128 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7124 96 128) (extract v_7126 96 128) (extract v_7128 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3244 : reg (bv 256)) (v_3245 : reg (bv 256)) (v_3246 : reg (bv 256)) => do
      v_7152 <- getRegister v_3245;
      v_7154 <- getRegister v_3246;
      v_7156 <- getRegister v_3244;
      setRegister (lhs.of_reg v_3246) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 0 32) (extract v_7154 0 32) (extract v_7156 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 32 64) (extract v_7154 32 64) (extract v_7156 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 64 96) (extract v_7154 64 96) (extract v_7156 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 96 128) (extract v_7154 96 128) (extract v_7156 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 128 160) (extract v_7154 128 160) (extract v_7156 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 160 192) (extract v_7154 160 192) (extract v_7156 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 192 224) (extract v_7154 192 224) (extract v_7156 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_7152 224 256) (extract v_7154 224 256) (extract v_7156 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_3229 : Mem) (v_3227 : reg (bv 128)) (v_3228 : reg (bv 128)) => do
      v_12829 <- getRegister v_3227;
      v_12831 <- getRegister v_3228;
      v_12833 <- evaluateAddress v_3229;
      v_12834 <- load v_12833 16;
      setRegister (lhs.of_reg v_3228) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12829 0 32) (extract v_12831 0 32) (extract v_12834 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12829 32 64) (extract v_12831 32 64) (extract v_12834 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12829 64 96) (extract v_12831 64 96) (extract v_12834 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12829 96 128) (extract v_12831 96 128) (extract v_12834 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3238 : Mem) (v_3239 : reg (bv 256)) (v_3240 : reg (bv 256)) => do
      v_12853 <- getRegister v_3239;
      v_12855 <- getRegister v_3240;
      v_12857 <- evaluateAddress v_3238;
      v_12858 <- load v_12857 32;
      setRegister (lhs.of_reg v_3240) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 0 32) (extract v_12855 0 32) (extract v_12858 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 32 64) (extract v_12855 32 64) (extract v_12858 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 64 96) (extract v_12855 64 96) (extract v_12858 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 96 128) (extract v_12855 96 128) (extract v_12858 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 128 160) (extract v_12855 128 160) (extract v_12858 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 160 192) (extract v_12855 160 192) (extract v_12858 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 192 224) (extract v_12855 192 224) (extract v_12858 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12853 224 256) (extract v_12855 224 256) (extract v_12858 224 256))))));
      pure ()
    pat_end
