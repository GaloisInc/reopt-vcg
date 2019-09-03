def vfnmadd213ps1 : instruction :=
  definst "vfnmadd213ps" $ do
    pattern fun (v_3179 : reg (bv 128)) (v_3180 : reg (bv 128)) (v_3181 : reg (bv 128)) => do
      v_10746 <- getRegister v_3180;
      v_10748 <- getRegister v_3179;
      v_10750 <- getRegister v_3181;
      setRegister (lhs.of_reg v_3181) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10746 0 32) (extract v_10748 0 32) (extract v_10750 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10746 32 64) (extract v_10748 32 64) (extract v_10750 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10746 64 96) (extract v_10748 64 96) (extract v_10750 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10746 96 128) (extract v_10748 96 128) (extract v_10750 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3190 : reg (bv 256)) (v_3191 : reg (bv 256)) (v_3192 : reg (bv 256)) => do
      v_10774 <- getRegister v_3191;
      v_10776 <- getRegister v_3190;
      v_10778 <- getRegister v_3192;
      setRegister (lhs.of_reg v_3192) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 0 32) (extract v_10776 0 32) (extract v_10778 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 32 64) (extract v_10776 32 64) (extract v_10778 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 64 96) (extract v_10776 64 96) (extract v_10778 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 96 128) (extract v_10776 96 128) (extract v_10778 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 128 160) (extract v_10776 128 160) (extract v_10778 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 160 192) (extract v_10776 160 192) (extract v_10778 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 192 224) (extract v_10776 192 224) (extract v_10778 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_10774 224 256) (extract v_10776 224 256) (extract v_10778 224 256))))))));
      pure ()
    pat_end;
    pattern fun (v_3176 : Mem) (v_3174 : reg (bv 128)) (v_3175 : reg (bv 128)) => do
      v_21409 <- getRegister v_3174;
      v_21411 <- evaluateAddress v_3176;
      v_21412 <- load v_21411 16;
      v_21414 <- getRegister v_3175;
      setRegister (lhs.of_reg v_3175) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21409 0 32) (extract v_21412 0 32) (extract v_21414 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21409 32 64) (extract v_21412 32 64) (extract v_21414 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21409 64 96) (extract v_21412 64 96) (extract v_21414 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21409 96 128) (extract v_21412 96 128) (extract v_21414 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3185 : Mem) (v_3186 : reg (bv 256)) (v_3187 : reg (bv 256)) => do
      v_21433 <- getRegister v_3186;
      v_21435 <- evaluateAddress v_3185;
      v_21436 <- load v_21435 32;
      v_21438 <- getRegister v_3187;
      setRegister (lhs.of_reg v_3187) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 0 32) (extract v_21436 0 32) (extract v_21438 0 32)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 32 64) (extract v_21436 32 64) (extract v_21438 32 64))) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 64 96) (extract v_21436 64 96) (extract v_21438 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 96 128) (extract v_21436 96 128) (extract v_21438 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 128 160) (extract v_21436 128 160) (extract v_21438 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 160 192) (extract v_21436 160 192) (extract v_21438 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 192 224) (extract v_21436 192 224) (extract v_21438 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_21433 224 256) (extract v_21436 224 256) (extract v_21438 224 256))))))));
      pure ()
    pat_end
