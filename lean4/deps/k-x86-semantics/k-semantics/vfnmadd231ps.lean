def vfnmadd231ps1 : instruction :=
  definst "vfnmadd231ps" $ do
    pattern fun (v_3245 : reg (bv 128)) (v_3246 : reg (bv 128)) (v_3247 : reg (bv 128)) => do
      v_10898 <- getRegister v_3246;
      v_10900 <- getRegister v_3247;
      v_10902 <- getRegister v_3245;
      setRegister (lhs.of_reg v_3247) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10898 0 32) (extract v_10900 0 32) (extract v_10902 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10898 32 64) (extract v_10900 32 64) (extract v_10902 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10898 64 96) (extract v_10900 64 96) (extract v_10902 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10898 96 128) (extract v_10900 96 128) (extract v_10902 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3256 : reg (bv 256)) (v_3257 : reg (bv 256)) (v_3258 : reg (bv 256)) => do
      v_10926 <- getRegister v_3257;
      v_10928 <- getRegister v_3258;
      v_10930 <- getRegister v_3256;
      setRegister (lhs.of_reg v_3258) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 0 32) (extract v_10928 0 32) (extract v_10930 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 32 64) (extract v_10928 32 64) (extract v_10930 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 64 96) (extract v_10928 64 96) (extract v_10930 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 96 128) (extract v_10928 96 128) (extract v_10930 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 128 160) (extract v_10928 128 160) (extract v_10930 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 160 192) (extract v_10928 160 192) (extract v_10930 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 192 224) (extract v_10928 192 224) (extract v_10930 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10926 224 256) (extract v_10928 224 256) (extract v_10930 224 256))))));
      pure ()
    pat_end;
    pattern fun (v_3242 : Mem) (v_3240 : reg (bv 128)) (v_3241 : reg (bv 128)) => do
      v_21535 <- getRegister v_3240;
      v_21537 <- getRegister v_3241;
      v_21539 <- evaluateAddress v_3242;
      v_21540 <- load v_21539 16;
      setRegister (lhs.of_reg v_3241) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21535 0 32) (extract v_21537 0 32) (extract v_21540 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21535 32 64) (extract v_21537 32 64) (extract v_21540 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21535 64 96) (extract v_21537 64 96) (extract v_21540 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21535 96 128) (extract v_21537 96 128) (extract v_21540 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3251 : Mem) (v_3252 : reg (bv 256)) (v_3253 : reg (bv 256)) => do
      v_21559 <- getRegister v_3252;
      v_21561 <- getRegister v_3253;
      v_21563 <- evaluateAddress v_3251;
      v_21564 <- load v_21563 32;
      setRegister (lhs.of_reg v_3253) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 0 32) (extract v_21561 0 32) (extract v_21564 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 32 64) (extract v_21561 32 64) (extract v_21564 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 64 96) (extract v_21561 64 96) (extract v_21564 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 96 128) (extract v_21561 96 128) (extract v_21564 96 128))))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 128 160) (extract v_21561 128 160) (extract v_21564 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 160 192) (extract v_21561 160 192) (extract v_21564 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 192 224) (extract v_21561 192 224) (extract v_21564 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21559 224 256) (extract v_21561 224 256) (extract v_21564 224 256))))));
      pure ()
    pat_end
