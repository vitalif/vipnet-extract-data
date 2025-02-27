### Извлечение закрытого ключа из контейнера VipNet

Поддерживает ключи по ГОСТ Р 34.10-2001 и ГОСТ Р 34.10-2012.

Аналогичные утилиты для КриптоПро: https://github.com/kmvi/cp-extract-data

#### VipNetExtract2

Извлечение закрытого ключа из файлового контейнера. Не требует наличия установленного VipNet CSP.

Примеры:

- `extractpkey -f c:\Users\username\AppData\Local\Infotecs\Containers\rnd-2-3673-B18F-494C-8112-317A-A468-1D53 -p 12345678 > pkey.pem` - указывается путь до контейнера и пароль (если имеется).

Поддерживает

- Ключевые контейнеры ViPNet CSP
- Ключевые контейнеры ViPNet JCrypto SDK (отличаются от CSP-шных использованием PBKDF2)
- Ключевые контейнеры ViPNet JCrypto SDK с ключами, зашифрованными не паролем, а ключом из дополнительного ключевого контейнера

### Авторы

- https://github.com/kmvi - оригинальная утилита
- https://github.com/vitalif - поддержка ключей JCrypto SDK
